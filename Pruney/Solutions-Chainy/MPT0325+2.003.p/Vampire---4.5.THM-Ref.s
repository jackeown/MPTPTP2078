%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:37 EST 2020

% Result     : Theorem 22.59s
% Output     : Refutation 22.59s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 895 expanded)
%              Number of leaves         :   27 ( 290 expanded)
%              Depth                    :   21
%              Number of atoms          :  231 (1250 expanded)
%              Number of equality atoms :  134 ( 904 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6247,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6246,f4787])).

fof(f4787,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f4685,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f4685,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f3488,f4553])).

fof(f4553,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f4552,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f55,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f74,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f78,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f4552,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f4551,f88])).

fof(f4551,plain,(
    k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3)))) ),
    inference(forward_demodulation,[],[f4472,f1279])).

fof(f1279,plain,(
    ! [X4,X5,X3] : k2_zfmisc_1(X3,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) = k2_zfmisc_1(X3,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4))) ),
    inference(superposition,[],[f202,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f73,f86,f86])).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f202,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X1))) ),
    inference(superposition,[],[f93,f87])).

fof(f87,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f54,f85,f85])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f4472,plain,(
    k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k3_tarski(k6_enumset1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),sK1))) ),
    inference(superposition,[],[f1719,f202])).

fof(f1719,plain,(
    ! [X0] : k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK3)) = k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)))) ),
    inference(forward_demodulation,[],[f1698,f87])).

fof(f1698,plain,(
    ! [X0] : k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK3)) = k3_tarski(k6_enumset1(k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f215,f102])).

fof(f102,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f46,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f46,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f215,plain,(
    ! [X6,X4,X8,X7,X5] : k2_zfmisc_1(k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,k3_xboole_0(X4,X5))),k3_xboole_0(X6,X7)) = k3_tarski(k6_enumset1(k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)))) ),
    inference(superposition,[],[f94,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f94,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f72,f86,f86])).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f3488,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f2288,f3485])).

fof(f3485,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f2985,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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

fof(f2985,plain,(
    ~ r1_xboole_0(sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f1888,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f1888,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f98,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(superposition,[],[f60,f102])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f98,plain,(
    r2_hidden(sK4(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f97,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f97,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f47,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f2288,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f66,f720])).

fof(f720,plain,(
    k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f184,f102])).

fof(f184,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X2,X3)) = k5_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(superposition,[],[f162,f75])).

fof(f162,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f92,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f75,f53])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f92,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f70,f58,f58])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f6246,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f6245,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f58])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f6245,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(subsumption_resolution,[],[f48,f6238])).

fof(f6238,plain,(
    r1_tarski(sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f4306,f90])).

fof(f4306,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f4205,f49])).

fof(f4205,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(backward_demodulation,[],[f3986,f4071])).

fof(f4071,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f4070,f88])).

fof(f4070,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3)))) ),
    inference(forward_demodulation,[],[f4069,f88])).

fof(f4069,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,sK2))),sK1) ),
    inference(forward_demodulation,[],[f3992,f1457])).

fof(f1457,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X9)),X8) = k2_zfmisc_1(k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X7)),X8) ),
    inference(superposition,[],[f216,f94])).

fof(f216,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X0,X1))) ),
    inference(superposition,[],[f94,f87])).

fof(f3992,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k3_tarski(k6_enumset1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),sK0)),sK1) ),
    inference(superposition,[],[f1658,f216])).

fof(f1658,plain,(
    ! [X0] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,sK3)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0))) ),
    inference(forward_demodulation,[],[f1639,f87])).

fof(f1639,plain,(
    ! [X0] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,sK3)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f201,f102])).

fof(f201,plain,(
    ! [X6,X4,X8,X7,X5] : k2_zfmisc_1(k3_xboole_0(X4,X5),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,k3_xboole_0(X6,X7)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)))) ),
    inference(superposition,[],[f93,f75])).

fof(f3986,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f2217,f3983])).

fof(f3983,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f2986,f63])).

fof(f2986,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f1888,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2217,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f66,f679])).

fof(f679,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f169,f102])).

fof(f169,plain,(
    ! [X4,X2,X5,X3] : k2_zfmisc_1(k3_xboole_0(X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,X5))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X2,X3),X4),k3_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X5))) ),
    inference(superposition,[],[f161,f75])).

fof(f161,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f91,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f75,f53])).

fof(f91,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f71,f58,f58])).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (31196)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (31194)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (31209)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (31203)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (31201)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (31205)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (31206)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (31200)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (31195)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (31219)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (31222)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (31198)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (31208)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (31210)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (31214)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (31216)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (31221)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (31218)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (31204)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (31213)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.56  % (31202)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (31216)Refutation not found, incomplete strategy% (31216)------------------------------
% 0.20/0.56  % (31216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (31216)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (31216)Memory used [KB]: 10746
% 0.20/0.56  % (31216)Time elapsed: 0.142 s
% 0.20/0.56  % (31216)------------------------------
% 0.20/0.56  % (31216)------------------------------
% 0.20/0.56  % (31223)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (31217)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.57  % (31197)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.58  % (31215)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.58  % (31220)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.59  % (31212)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.75/0.59  % (31207)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.75/0.60  % (31211)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.75/0.60  % (31211)Refutation not found, incomplete strategy% (31211)------------------------------
% 1.75/0.60  % (31211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (31211)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.60  
% 1.75/0.60  % (31211)Memory used [KB]: 10618
% 1.75/0.60  % (31211)Time elapsed: 0.169 s
% 1.75/0.60  % (31211)------------------------------
% 1.75/0.60  % (31211)------------------------------
% 1.75/0.60  % (31199)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 2.09/0.70  % (31224)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.09/0.71  % (31225)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.16/0.85  % (31199)Time limit reached!
% 3.16/0.85  % (31199)------------------------------
% 3.16/0.85  % (31199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.85  % (31199)Termination reason: Time limit
% 3.16/0.85  % (31199)Termination phase: Saturation
% 3.16/0.85  
% 3.16/0.85  % (31199)Memory used [KB]: 8315
% 3.16/0.85  % (31199)Time elapsed: 0.400 s
% 3.16/0.85  % (31199)------------------------------
% 3.16/0.85  % (31199)------------------------------
% 3.97/0.91  % (31204)Time limit reached!
% 3.97/0.91  % (31204)------------------------------
% 3.97/0.91  % (31204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/0.91  % (31204)Termination reason: Time limit
% 3.97/0.91  
% 3.97/0.91  % (31204)Memory used [KB]: 14200
% 3.97/0.91  % (31204)Time elapsed: 0.507 s
% 3.97/0.91  % (31204)------------------------------
% 3.97/0.91  % (31204)------------------------------
% 3.97/0.91  % (31194)Time limit reached!
% 3.97/0.91  % (31194)------------------------------
% 3.97/0.91  % (31194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.93  % (31194)Termination reason: Time limit
% 4.31/0.93  % (31206)Time limit reached!
% 4.31/0.93  % (31206)------------------------------
% 4.31/0.93  % (31206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.93  % (31206)Termination reason: Time limit
% 4.31/0.93  
% 4.31/0.93  % (31206)Memory used [KB]: 10490
% 4.31/0.93  % (31206)Time elapsed: 0.520 s
% 4.31/0.93  % (31206)------------------------------
% 4.31/0.93  % (31206)------------------------------
% 4.31/0.93  % (31194)Termination phase: Saturation
% 4.31/0.93  
% 4.31/0.93  % (31194)Memory used [KB]: 5500
% 4.31/0.93  % (31194)Time elapsed: 0.500 s
% 4.31/0.93  % (31194)------------------------------
% 4.31/0.93  % (31194)------------------------------
% 4.31/0.93  % (31195)Time limit reached!
% 4.31/0.93  % (31195)------------------------------
% 4.31/0.93  % (31195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.95  % (31195)Termination reason: Time limit
% 4.31/0.95  
% 4.31/0.95  % (31195)Memory used [KB]: 9083
% 4.31/0.95  % (31195)Time elapsed: 0.525 s
% 4.31/0.95  % (31195)------------------------------
% 4.31/0.95  % (31195)------------------------------
% 4.31/0.99  % (31226)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.31/1.01  % (31210)Time limit reached!
% 4.31/1.01  % (31210)------------------------------
% 4.31/1.01  % (31210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.88/1.02  % (31210)Termination reason: Time limit
% 4.88/1.02  
% 4.88/1.02  % (31210)Memory used [KB]: 16502
% 4.88/1.02  % (31210)Time elapsed: 0.609 s
% 4.88/1.02  % (31210)------------------------------
% 4.88/1.02  % (31210)------------------------------
% 4.88/1.02  % (31201)Time limit reached!
% 4.88/1.02  % (31201)------------------------------
% 4.88/1.02  % (31201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.88/1.02  % (31201)Termination reason: Time limit
% 4.88/1.02  
% 4.88/1.02  % (31201)Memory used [KB]: 10618
% 4.88/1.02  % (31201)Time elapsed: 0.617 s
% 4.88/1.02  % (31201)------------------------------
% 4.88/1.02  % (31201)------------------------------
% 4.88/1.03  % (31222)Time limit reached!
% 4.88/1.03  % (31222)------------------------------
% 4.88/1.03  % (31222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.88/1.03  % (31222)Termination reason: Time limit
% 4.88/1.03  % (31222)Termination phase: Saturation
% 4.88/1.03  
% 4.88/1.03  % (31222)Memory used [KB]: 9850
% 4.88/1.03  % (31222)Time elapsed: 0.600 s
% 4.88/1.03  % (31222)------------------------------
% 4.88/1.03  % (31222)------------------------------
% 4.88/1.03  % (31227)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.88/1.07  % (31228)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.31/1.08  % (31230)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.31/1.09  % (31229)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.31/1.12  % (31231)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.31/1.15  % (31233)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.31/1.15  % (31232)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.82/1.24  % (31215)Time limit reached!
% 6.82/1.24  % (31215)------------------------------
% 6.82/1.24  % (31215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.82/1.24  % (31215)Termination reason: Time limit
% 6.82/1.24  
% 6.82/1.24  % (31215)Memory used [KB]: 7291
% 6.82/1.24  % (31215)Time elapsed: 0.802 s
% 6.82/1.24  % (31215)------------------------------
% 6.82/1.24  % (31215)------------------------------
% 7.40/1.34  % (31227)Time limit reached!
% 7.40/1.34  % (31227)------------------------------
% 7.40/1.34  % (31227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.40/1.34  % (31227)Termination reason: Time limit
% 7.40/1.34  
% 7.40/1.34  % (31227)Memory used [KB]: 7291
% 7.40/1.34  % (31227)Time elapsed: 0.404 s
% 7.40/1.34  % (31227)------------------------------
% 7.40/1.34  % (31227)------------------------------
% 7.96/1.38  % (31234)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.96/1.39  % (31228)Time limit reached!
% 7.96/1.39  % (31228)------------------------------
% 7.96/1.39  % (31228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.96/1.39  % (31228)Termination reason: Time limit
% 7.96/1.39  % (31228)Termination phase: Saturation
% 7.96/1.39  
% 7.96/1.39  % (31228)Memory used [KB]: 13560
% 7.96/1.39  % (31228)Time elapsed: 0.400 s
% 7.96/1.39  % (31228)------------------------------
% 7.96/1.39  % (31228)------------------------------
% 7.96/1.43  % (31196)Time limit reached!
% 7.96/1.43  % (31196)------------------------------
% 7.96/1.43  % (31196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.96/1.43  % (31196)Termination reason: Time limit
% 7.96/1.43  
% 7.96/1.43  % (31196)Memory used [KB]: 19957
% 7.96/1.43  % (31196)Time elapsed: 1.020 s
% 7.96/1.43  % (31196)------------------------------
% 7.96/1.43  % (31196)------------------------------
% 8.84/1.50  % (31235)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.84/1.52  % (31236)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.61/1.61  % (31237)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.61/1.65  % (31220)Time limit reached!
% 9.61/1.65  % (31220)------------------------------
% 9.61/1.65  % (31220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.61/1.67  % (31220)Termination reason: Time limit
% 9.61/1.67  
% 9.61/1.67  % (31220)Memory used [KB]: 19829
% 9.61/1.67  % (31220)Time elapsed: 1.230 s
% 9.61/1.67  % (31220)------------------------------
% 9.61/1.67  % (31220)------------------------------
% 10.40/1.71  % (31209)Time limit reached!
% 10.40/1.71  % (31209)------------------------------
% 10.40/1.71  % (31209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.40/1.71  % (31209)Termination reason: Time limit
% 10.40/1.71  % (31209)Termination phase: Saturation
% 10.40/1.71  
% 10.40/1.71  % (31209)Memory used [KB]: 18933
% 10.40/1.71  % (31209)Time elapsed: 1.304 s
% 10.40/1.71  % (31209)------------------------------
% 10.40/1.71  % (31209)------------------------------
% 10.40/1.72  % (31218)Time limit reached!
% 10.40/1.72  % (31218)------------------------------
% 10.40/1.72  % (31218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.40/1.73  % (31218)Termination reason: Time limit
% 10.40/1.73  % (31218)Termination phase: Saturation
% 10.40/1.73  
% 10.40/1.73  % (31218)Memory used [KB]: 25202
% 10.40/1.73  % (31218)Time elapsed: 1.300 s
% 10.40/1.73  % (31218)------------------------------
% 10.40/1.73  % (31218)------------------------------
% 11.11/1.79  % (31250)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.48/1.83  % (31277)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.48/1.84  % (31265)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 12.14/1.93  % (31236)Time limit reached!
% 12.14/1.93  % (31236)------------------------------
% 12.14/1.93  % (31236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.14/1.94  % (31221)Time limit reached!
% 12.14/1.94  % (31221)------------------------------
% 12.14/1.94  % (31221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.14/1.94  % (31221)Termination reason: Time limit
% 12.14/1.94  % (31221)Termination phase: Saturation
% 12.14/1.94  
% 12.14/1.94  % (31221)Memory used [KB]: 14456
% 12.14/1.94  % (31221)Time elapsed: 1.500 s
% 12.14/1.94  % (31221)------------------------------
% 12.14/1.94  % (31221)------------------------------
% 12.14/1.94  % (31236)Termination reason: Time limit
% 12.14/1.94  
% 12.14/1.94  % (31236)Memory used [KB]: 4733
% 12.14/1.94  % (31236)Time elapsed: 0.524 s
% 12.14/1.94  % (31236)------------------------------
% 12.14/1.94  % (31236)------------------------------
% 12.14/1.95  % (31198)Time limit reached!
% 12.14/1.95  % (31198)------------------------------
% 12.14/1.95  % (31198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.14/1.95  % (31198)Termination reason: Time limit
% 12.14/1.95  
% 12.14/1.95  % (31198)Memory used [KB]: 13816
% 12.14/1.95  % (31198)Time elapsed: 1.532 s
% 12.14/1.95  % (31198)------------------------------
% 12.14/1.95  % (31198)------------------------------
% 12.64/2.07  % (31381)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 13.22/2.07  % (31384)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.24/2.08  % (31389)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.54/2.19  % (31230)Time limit reached!
% 13.54/2.19  % (31230)------------------------------
% 13.54/2.19  % (31230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.54/2.19  % (31205)Time limit reached!
% 13.54/2.19  % (31205)------------------------------
% 13.54/2.19  % (31205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.54/2.19  % (31205)Termination reason: Time limit
% 13.54/2.19  % (31205)Termination phase: Saturation
% 13.54/2.19  
% 13.54/2.19  % (31205)Memory used [KB]: 21492
% 13.54/2.19  % (31205)Time elapsed: 1.600 s
% 13.54/2.19  % (31205)------------------------------
% 13.54/2.19  % (31205)------------------------------
% 13.54/2.20  % (31230)Termination reason: Time limit
% 13.54/2.21  
% 13.54/2.21  % (31230)Memory used [KB]: 14583
% 13.54/2.21  % (31230)Time elapsed: 1.216 s
% 13.54/2.21  % (31230)------------------------------
% 13.54/2.21  % (31230)------------------------------
% 13.54/2.21  % (31277)Time limit reached!
% 13.54/2.21  % (31277)------------------------------
% 13.54/2.21  % (31277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.54/2.21  % (31277)Termination reason: Time limit
% 13.54/2.21  % (31277)Termination phase: Saturation
% 13.54/2.21  
% 13.54/2.21  % (31277)Memory used [KB]: 4477
% 13.54/2.21  % (31277)Time elapsed: 0.400 s
% 13.54/2.21  % (31277)------------------------------
% 13.54/2.21  % (31277)------------------------------
% 14.30/2.25  % (31208)Time limit reached!
% 14.30/2.25  % (31208)------------------------------
% 14.30/2.25  % (31208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.30/2.25  % (31208)Termination reason: Time limit
% 14.30/2.25  % (31208)Termination phase: Saturation
% 14.30/2.25  
% 14.30/2.25  % (31208)Memory used [KB]: 4861
% 14.30/2.25  % (31208)Time elapsed: 1.800 s
% 14.30/2.25  % (31208)------------------------------
% 14.30/2.25  % (31208)------------------------------
% 15.37/2.30  % (31469)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.37/2.32  % (31477)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 15.37/2.33  % (31471)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.37/2.33  % (31461)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 16.03/2.40  % (31389)Time limit reached!
% 16.03/2.40  % (31389)------------------------------
% 16.03/2.40  % (31389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.03/2.40  % (31389)Termination reason: Time limit
% 16.03/2.40  % (31389)Termination phase: Saturation
% 16.03/2.40  
% 16.03/2.40  % (31389)Memory used [KB]: 2814
% 16.03/2.40  % (31389)Time elapsed: 0.400 s
% 16.03/2.40  % (31389)------------------------------
% 16.03/2.40  % (31389)------------------------------
% 16.29/2.45  % (31212)Time limit reached!
% 16.29/2.45  % (31212)------------------------------
% 16.29/2.45  % (31212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.29/2.45  % (31212)Termination reason: Time limit
% 16.29/2.45  
% 16.29/2.45  % (31212)Memory used [KB]: 16630
% 16.29/2.45  % (31212)Time elapsed: 2.029 s
% 16.29/2.45  % (31212)------------------------------
% 16.29/2.45  % (31212)------------------------------
% 16.29/2.49  % (31478)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.98/2.52  % (31200)Time limit reached!
% 16.98/2.52  % (31200)------------------------------
% 16.98/2.52  % (31200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.98/2.52  % (31200)Termination reason: Time limit
% 16.98/2.52  
% 16.98/2.52  % (31200)Memory used [KB]: 28272
% 16.98/2.52  % (31200)Time elapsed: 2.077 s
% 16.98/2.52  % (31200)------------------------------
% 16.98/2.52  % (31200)------------------------------
% 16.98/2.54  % (31479)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 17.59/2.60  % (31226)Time limit reached!
% 17.59/2.60  % (31226)------------------------------
% 17.59/2.60  % (31226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.59/2.60  % (31226)Termination reason: Time limit
% 17.59/2.60  % (31226)Termination phase: Saturation
% 17.59/2.60  
% 17.59/2.60  % (31226)Memory used [KB]: 20212
% 17.59/2.60  % (31226)Time elapsed: 1.700 s
% 17.59/2.60  % (31226)------------------------------
% 17.59/2.60  % (31226)------------------------------
% 17.59/2.65  % (31480)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 18.46/2.73  % (31481)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 19.51/2.84  % (31232)Time limit reached!
% 19.51/2.84  % (31232)------------------------------
% 19.51/2.84  % (31232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.51/2.85  % (31478)Time limit reached!
% 19.51/2.85  % (31478)------------------------------
% 19.51/2.85  % (31478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.51/2.86  % (31232)Termination reason: Time limit
% 19.51/2.86  
% 19.51/2.86  % (31232)Memory used [KB]: 19445
% 19.51/2.86  % (31232)Time elapsed: 1.756 s
% 19.51/2.86  % (31232)------------------------------
% 19.51/2.86  % (31232)------------------------------
% 19.51/2.87  % (31478)Termination reason: Time limit
% 19.51/2.87  
% 19.51/2.87  % (31478)Memory used [KB]: 13432
% 19.51/2.87  % (31478)Time elapsed: 0.421 s
% 19.51/2.87  % (31478)------------------------------
% 19.51/2.87  % (31478)------------------------------
% 20.18/2.94  % (31202)Time limit reached!
% 20.18/2.94  % (31202)------------------------------
% 20.18/2.94  % (31202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.18/2.94  % (31202)Termination reason: Time limit
% 20.18/2.94  
% 20.18/2.94  % (31202)Memory used [KB]: 28656
% 20.18/2.94  % (31202)Time elapsed: 2.529 s
% 20.18/2.94  % (31202)------------------------------
% 20.18/2.94  % (31202)------------------------------
% 20.18/2.95  % (31480)Time limit reached!
% 20.18/2.95  % (31480)------------------------------
% 20.18/2.95  % (31480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.18/2.96  % (31265)Time limit reached!
% 20.18/2.96  % (31265)------------------------------
% 20.18/2.96  % (31265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.18/2.96  % (31265)Termination reason: Time limit
% 20.18/2.96  
% 20.18/2.96  % (31265)Memory used [KB]: 18038
% 20.18/2.96  % (31265)Time elapsed: 1.228 s
% 20.18/2.96  % (31265)------------------------------
% 20.18/2.96  % (31265)------------------------------
% 20.18/2.96  % (31480)Termination reason: Time limit
% 20.18/2.96  % (31480)Termination phase: Saturation
% 20.18/2.96  
% 20.18/2.96  % (31480)Memory used [KB]: 11641
% 20.18/2.96  % (31480)Time elapsed: 0.400 s
% 20.18/2.96  % (31480)------------------------------
% 20.18/2.96  % (31480)------------------------------
% 20.92/2.99  % (31213)Time limit reached!
% 20.92/2.99  % (31213)------------------------------
% 20.92/2.99  % (31213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.92/3.01  % (31213)Termination reason: Time limit
% 20.92/3.01  % (31213)Termination phase: Saturation
% 20.92/3.01  
% 20.92/3.01  % (31213)Memory used [KB]: 41065
% 20.92/3.01  % (31213)Time elapsed: 2.600 s
% 20.92/3.01  % (31213)------------------------------
% 20.92/3.01  % (31213)------------------------------
% 22.59/3.22  % (31469)Refutation found. Thanks to Tanya!
% 22.59/3.22  % SZS status Theorem for theBenchmark
% 22.59/3.22  % SZS output start Proof for theBenchmark
% 22.59/3.22  fof(f6247,plain,(
% 22.59/3.22    $false),
% 22.59/3.22    inference(subsumption_resolution,[],[f6246,f4787])).
% 22.59/3.22  fof(f4787,plain,(
% 22.59/3.22    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 22.59/3.22    inference(subsumption_resolution,[],[f4685,f49])).
% 22.59/3.22  fof(f49,plain,(
% 22.59/3.22    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f10])).
% 22.59/3.22  fof(f10,axiom,(
% 22.59/3.22    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 22.59/3.22  fof(f4685,plain,(
% 22.59/3.22    k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 22.59/3.22    inference(backward_demodulation,[],[f3488,f4553])).
% 22.59/3.22  fof(f4553,plain,(
% 22.59/3.22    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 22.59/3.22    inference(forward_demodulation,[],[f4552,f88])).
% 22.59/3.22  fof(f88,plain,(
% 22.59/3.22    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 22.59/3.22    inference(definition_unfolding,[],[f55,f86])).
% 22.59/3.22  fof(f86,plain,(
% 22.59/3.22    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 22.59/3.22    inference(definition_unfolding,[],[f57,f85])).
% 22.59/3.22  fof(f85,plain,(
% 22.59/3.22    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 22.59/3.22    inference(definition_unfolding,[],[f56,f84])).
% 22.59/3.22  fof(f84,plain,(
% 22.59/3.22    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 22.59/3.22    inference(definition_unfolding,[],[f69,f83])).
% 22.59/3.22  fof(f83,plain,(
% 22.59/3.22    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 22.59/3.22    inference(definition_unfolding,[],[f74,f82])).
% 22.59/3.22  fof(f82,plain,(
% 22.59/3.22    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 22.59/3.22    inference(definition_unfolding,[],[f78,f81])).
% 22.59/3.22  fof(f81,plain,(
% 22.59/3.22    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 22.59/3.22    inference(definition_unfolding,[],[f79,f80])).
% 22.59/3.22  fof(f80,plain,(
% 22.59/3.22    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f17])).
% 22.59/3.22  fof(f17,axiom,(
% 22.59/3.22    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 22.59/3.22  fof(f79,plain,(
% 22.59/3.22    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f16])).
% 22.59/3.22  fof(f16,axiom,(
% 22.59/3.22    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 22.59/3.22  fof(f78,plain,(
% 22.59/3.22    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f15])).
% 22.59/3.22  fof(f15,axiom,(
% 22.59/3.22    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 22.59/3.22  fof(f74,plain,(
% 22.59/3.22    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f14])).
% 22.59/3.22  fof(f14,axiom,(
% 22.59/3.22    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 22.59/3.22  fof(f69,plain,(
% 22.59/3.22    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f13])).
% 22.59/3.22  fof(f13,axiom,(
% 22.59/3.22    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 22.59/3.22  fof(f56,plain,(
% 22.59/3.22    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f12])).
% 22.59/3.22  fof(f12,axiom,(
% 22.59/3.22    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 22.59/3.22  fof(f57,plain,(
% 22.59/3.22    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f18])).
% 22.59/3.22  fof(f18,axiom,(
% 22.59/3.22    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 22.59/3.22  fof(f55,plain,(
% 22.59/3.22    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 22.59/3.22    inference(cnf_transformation,[],[f8])).
% 22.59/3.22  fof(f8,axiom,(
% 22.59/3.22    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 22.59/3.22  fof(f4552,plain,(
% 22.59/3.22    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK3))),
% 22.59/3.22    inference(forward_demodulation,[],[f4551,f88])).
% 22.59/3.22  fof(f4551,plain,(
% 22.59/3.22    k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3))))),
% 22.59/3.22    inference(forward_demodulation,[],[f4472,f1279])).
% 22.59/3.22  fof(f1279,plain,(
% 22.59/3.22    ( ! [X4,X5,X3] : (k2_zfmisc_1(X3,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) = k2_zfmisc_1(X3,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)))) )),
% 22.59/3.22    inference(superposition,[],[f202,f93])).
% 22.59/3.22  fof(f93,plain,(
% 22.59/3.22    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 22.59/3.22    inference(definition_unfolding,[],[f73,f86,f86])).
% 22.59/3.22  fof(f73,plain,(
% 22.59/3.22    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 22.59/3.22    inference(cnf_transformation,[],[f20])).
% 22.59/3.22  fof(f20,axiom,(
% 22.59/3.22    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 22.59/3.22  fof(f202,plain,(
% 22.59/3.22    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X1)))) )),
% 22.59/3.22    inference(superposition,[],[f93,f87])).
% 22.59/3.22  fof(f87,plain,(
% 22.59/3.22    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 22.59/3.22    inference(definition_unfolding,[],[f54,f85,f85])).
% 22.59/3.22  fof(f54,plain,(
% 22.59/3.22    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f11])).
% 22.59/3.22  fof(f11,axiom,(
% 22.59/3.22    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 22.59/3.22  fof(f4472,plain,(
% 22.59/3.22    k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k3_tarski(k6_enumset1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),sK1)))),
% 22.59/3.22    inference(superposition,[],[f1719,f202])).
% 22.59/3.22  fof(f1719,plain,(
% 22.59/3.22    ( ! [X0] : (k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK3)) = k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3))))) )),
% 22.59/3.22    inference(forward_demodulation,[],[f1698,f87])).
% 22.59/3.22  fof(f1698,plain,(
% 22.59/3.22    ( ! [X0] : (k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK3)) = k3_tarski(k6_enumset1(k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)))) )),
% 22.59/3.22    inference(superposition,[],[f215,f102])).
% 22.59/3.22  fof(f102,plain,(
% 22.59/3.22    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 22.59/3.22    inference(unit_resulting_resolution,[],[f46,f61])).
% 22.59/3.22  fof(f61,plain,(
% 22.59/3.22    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 22.59/3.22    inference(cnf_transformation,[],[f32])).
% 22.59/3.22  fof(f32,plain,(
% 22.59/3.22    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 22.59/3.22    inference(ennf_transformation,[],[f9])).
% 22.59/3.22  fof(f9,axiom,(
% 22.59/3.22    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 22.59/3.22  fof(f46,plain,(
% 22.59/3.22    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 22.59/3.22    inference(cnf_transformation,[],[f35])).
% 22.59/3.22  fof(f35,plain,(
% 22.59/3.22    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 22.59/3.22    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f34])).
% 22.59/3.22  fof(f34,plain,(
% 22.59/3.22    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 22.59/3.22    introduced(choice_axiom,[])).
% 22.59/3.22  fof(f29,plain,(
% 22.59/3.22    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 22.59/3.22    inference(flattening,[],[f28])).
% 22.59/3.22  fof(f28,plain,(
% 22.59/3.22    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 22.59/3.22    inference(ennf_transformation,[],[f25])).
% 22.59/3.22  fof(f25,negated_conjecture,(
% 22.59/3.22    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 22.59/3.22    inference(negated_conjecture,[],[f24])).
% 22.59/3.22  fof(f24,conjecture,(
% 22.59/3.22    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 22.59/3.22  fof(f215,plain,(
% 22.59/3.22    ( ! [X6,X4,X8,X7,X5] : (k2_zfmisc_1(k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,k3_xboole_0(X4,X5))),k3_xboole_0(X6,X7)) = k3_tarski(k6_enumset1(k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7))))) )),
% 22.59/3.22    inference(superposition,[],[f94,f75])).
% 22.59/3.22  fof(f75,plain,(
% 22.59/3.22    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 22.59/3.22    inference(cnf_transformation,[],[f21])).
% 22.59/3.22  fof(f21,axiom,(
% 22.59/3.22    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 22.59/3.22  fof(f94,plain,(
% 22.59/3.22    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 22.59/3.22    inference(definition_unfolding,[],[f72,f86,f86])).
% 22.59/3.22  fof(f72,plain,(
% 22.59/3.22    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 22.59/3.22    inference(cnf_transformation,[],[f20])).
% 22.59/3.22  fof(f3488,plain,(
% 22.59/3.22    k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 22.59/3.22    inference(subsumption_resolution,[],[f2288,f3485])).
% 22.59/3.22  fof(f3485,plain,(
% 22.59/3.22    k1_xboole_0 != k3_xboole_0(sK1,sK3)),
% 22.59/3.22    inference(unit_resulting_resolution,[],[f2985,f63])).
% 22.59/3.22  fof(f63,plain,(
% 22.59/3.22    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f42])).
% 22.59/3.22  fof(f42,plain,(
% 22.59/3.22    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 22.59/3.22    inference(nnf_transformation,[],[f2])).
% 22.59/3.22  fof(f2,axiom,(
% 22.59/3.22    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 22.59/3.22  fof(f2985,plain,(
% 22.59/3.22    ~r1_xboole_0(sK1,sK3)),
% 22.59/3.22    inference(unit_resulting_resolution,[],[f1888,f77])).
% 22.59/3.22  fof(f77,plain,(
% 22.59/3.22    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f33])).
% 22.59/3.22  fof(f33,plain,(
% 22.59/3.22    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 22.59/3.22    inference(ennf_transformation,[],[f23])).
% 22.59/3.22  fof(f23,axiom,(
% 22.59/3.22    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 22.59/3.22  fof(f1888,plain,(
% 22.59/3.22    ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 22.59/3.22    inference(unit_resulting_resolution,[],[f98,f110])).
% 22.59/3.22  fof(f110,plain,(
% 22.59/3.22    ( ! [X0] : (~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) )),
% 22.59/3.22    inference(superposition,[],[f60,f102])).
% 22.59/3.22  fof(f60,plain,(
% 22.59/3.22    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f41])).
% 22.59/3.22  fof(f41,plain,(
% 22.59/3.22    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 22.59/3.22    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f40])).
% 22.59/3.22  fof(f40,plain,(
% 22.59/3.22    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 22.59/3.22    introduced(choice_axiom,[])).
% 22.59/3.22  fof(f31,plain,(
% 22.59/3.22    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 22.59/3.22    inference(ennf_transformation,[],[f27])).
% 22.59/3.22  fof(f27,plain,(
% 22.59/3.22    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 22.59/3.22    inference(rectify,[],[f5])).
% 22.59/3.22  fof(f5,axiom,(
% 22.59/3.22    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 22.59/3.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 22.59/3.22  fof(f98,plain,(
% 22.59/3.22    r2_hidden(sK4(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 22.59/3.22    inference(unit_resulting_resolution,[],[f97,f52])).
% 22.59/3.22  fof(f52,plain,(
% 22.59/3.22    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 22.59/3.22    inference(cnf_transformation,[],[f39])).
% 22.59/3.22  fof(f39,plain,(
% 22.59/3.22    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 22.59/3.22    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 22.59/3.22  fof(f38,plain,(
% 22.59/3.22    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 22.59/3.22    introduced(choice_axiom,[])).
% 22.59/3.23  fof(f37,plain,(
% 22.59/3.23    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 22.59/3.23    inference(rectify,[],[f36])).
% 22.59/3.23  fof(f36,plain,(
% 22.59/3.23    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 22.59/3.23    inference(nnf_transformation,[],[f1])).
% 22.59/3.23  fof(f1,axiom,(
% 22.59/3.23    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 22.59/3.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 22.59/3.23  fof(f97,plain,(
% 22.59/3.23    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 22.59/3.23    inference(unit_resulting_resolution,[],[f47,f50])).
% 22.59/3.23  fof(f50,plain,(
% 22.59/3.23    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 22.59/3.23    inference(cnf_transformation,[],[f30])).
% 22.59/3.23  fof(f30,plain,(
% 22.59/3.23    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 22.59/3.23    inference(ennf_transformation,[],[f4])).
% 22.59/3.23  fof(f4,axiom,(
% 22.59/3.23    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 22.59/3.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 22.59/3.23  fof(f47,plain,(
% 22.59/3.23    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 22.59/3.23    inference(cnf_transformation,[],[f35])).
% 22.59/3.23  fof(f2288,plain,(
% 22.59/3.23    k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 22.59/3.23    inference(superposition,[],[f66,f720])).
% 22.59/3.23  fof(f720,plain,(
% 22.59/3.23    k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))),
% 22.59/3.23    inference(superposition,[],[f184,f102])).
% 22.59/3.23  fof(f184,plain,(
% 22.59/3.23    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X2,X3)) = k5_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 22.59/3.23    inference(superposition,[],[f162,f75])).
% 22.59/3.23  fof(f162,plain,(
% 22.59/3.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2))) )),
% 22.59/3.23    inference(backward_demodulation,[],[f92,f154])).
% 22.59/3.23  fof(f154,plain,(
% 22.59/3.23    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 22.59/3.23    inference(superposition,[],[f75,f53])).
% 22.59/3.23  fof(f53,plain,(
% 22.59/3.23    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 22.59/3.23    inference(cnf_transformation,[],[f26])).
% 22.59/3.23  fof(f26,plain,(
% 22.59/3.23    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 22.59/3.23    inference(rectify,[],[f3])).
% 22.59/3.23  fof(f3,axiom,(
% 22.59/3.23    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 22.59/3.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 22.59/3.23  fof(f92,plain,(
% 22.59/3.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 22.59/3.23    inference(definition_unfolding,[],[f70,f58,f58])).
% 22.59/3.23  fof(f58,plain,(
% 22.59/3.23    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 22.59/3.23    inference(cnf_transformation,[],[f7])).
% 22.59/3.23  fof(f7,axiom,(
% 22.59/3.23    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 22.59/3.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 22.59/3.23  fof(f70,plain,(
% 22.59/3.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 22.59/3.23    inference(cnf_transformation,[],[f22])).
% 22.59/3.23  fof(f22,axiom,(
% 22.59/3.23    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 22.59/3.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 22.59/3.23  fof(f66,plain,(
% 22.59/3.23    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 22.59/3.23    inference(cnf_transformation,[],[f45])).
% 22.59/3.23  fof(f45,plain,(
% 22.59/3.23    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 22.59/3.23    inference(flattening,[],[f44])).
% 22.59/3.23  fof(f44,plain,(
% 22.59/3.23    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 22.59/3.23    inference(nnf_transformation,[],[f19])).
% 22.59/3.23  fof(f19,axiom,(
% 22.59/3.23    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 22.59/3.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 22.59/3.23  fof(f6246,plain,(
% 22.59/3.23    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 22.59/3.23    inference(unit_resulting_resolution,[],[f6245,f90])).
% 22.59/3.23  fof(f90,plain,(
% 22.59/3.23    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 22.59/3.23    inference(definition_unfolding,[],[f64,f58])).
% 22.59/3.23  fof(f64,plain,(
% 22.59/3.23    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 22.59/3.23    inference(cnf_transformation,[],[f43])).
% 22.59/3.23  fof(f43,plain,(
% 22.59/3.23    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 22.59/3.23    inference(nnf_transformation,[],[f6])).
% 22.59/3.23  fof(f6,axiom,(
% 22.59/3.23    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 22.59/3.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 22.59/3.23  fof(f6245,plain,(
% 22.59/3.23    ~r1_tarski(sK0,sK2)),
% 22.59/3.23    inference(subsumption_resolution,[],[f48,f6238])).
% 22.59/3.23  fof(f6238,plain,(
% 22.59/3.23    r1_tarski(sK1,sK3)),
% 22.59/3.23    inference(unit_resulting_resolution,[],[f4306,f90])).
% 22.59/3.23  fof(f4306,plain,(
% 22.59/3.23    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 22.59/3.23    inference(subsumption_resolution,[],[f4205,f49])).
% 22.59/3.23  fof(f4205,plain,(
% 22.59/3.23    k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 22.59/3.23    inference(backward_demodulation,[],[f3986,f4071])).
% 22.59/3.23  fof(f4071,plain,(
% 22.59/3.23    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 22.59/3.23    inference(forward_demodulation,[],[f4070,f88])).
% 22.59/3.23  fof(f4070,plain,(
% 22.59/3.23    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3))))),
% 22.59/3.23    inference(forward_demodulation,[],[f4069,f88])).
% 22.59/3.23  fof(f4069,plain,(
% 22.59/3.23    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,sK2))),sK1)),
% 22.59/3.23    inference(forward_demodulation,[],[f3992,f1457])).
% 22.59/3.23  fof(f1457,plain,(
% 22.59/3.23    ( ! [X8,X7,X9] : (k2_zfmisc_1(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X9)),X8) = k2_zfmisc_1(k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X7)),X8)) )),
% 22.59/3.23    inference(superposition,[],[f216,f94])).
% 22.59/3.23  fof(f216,plain,(
% 22.59/3.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X0,X1)))) )),
% 22.59/3.23    inference(superposition,[],[f94,f87])).
% 22.59/3.23  fof(f3992,plain,(
% 22.59/3.23    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k3_tarski(k6_enumset1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),sK0)),sK1)),
% 22.59/3.23    inference(superposition,[],[f1658,f216])).
% 22.59/3.23  fof(f1658,plain,(
% 22.59/3.23    ( ! [X0] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,sK3)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0)))) )),
% 22.59/3.23    inference(forward_demodulation,[],[f1639,f87])).
% 22.59/3.23  fof(f1639,plain,(
% 22.59/3.23    ( ! [X0] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,sK3)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1)))) )),
% 22.59/3.23    inference(superposition,[],[f201,f102])).
% 22.59/3.23  fof(f201,plain,(
% 22.59/3.23    ( ! [X6,X4,X8,X7,X5] : (k2_zfmisc_1(k3_xboole_0(X4,X5),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,k3_xboole_0(X6,X7)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7))))) )),
% 22.59/3.23    inference(superposition,[],[f93,f75])).
% 22.59/3.23  fof(f3986,plain,(
% 22.59/3.23    k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 22.59/3.23    inference(subsumption_resolution,[],[f2217,f3983])).
% 22.59/3.23  fof(f3983,plain,(
% 22.59/3.23    k1_xboole_0 != k3_xboole_0(sK0,sK2)),
% 22.59/3.23    inference(unit_resulting_resolution,[],[f2986,f63])).
% 22.59/3.23  fof(f2986,plain,(
% 22.59/3.23    ~r1_xboole_0(sK0,sK2)),
% 22.59/3.23    inference(unit_resulting_resolution,[],[f1888,f76])).
% 22.59/3.23  fof(f76,plain,(
% 22.59/3.23    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 22.59/3.23    inference(cnf_transformation,[],[f33])).
% 22.59/3.23  fof(f2217,plain,(
% 22.59/3.23    k1_xboole_0 != k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 22.59/3.23    inference(superposition,[],[f66,f679])).
% 22.59/3.23  fof(f679,plain,(
% 22.59/3.23    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1))),
% 22.59/3.23    inference(superposition,[],[f169,f102])).
% 22.59/3.23  fof(f169,plain,(
% 22.59/3.23    ( ! [X4,X2,X5,X3] : (k2_zfmisc_1(k3_xboole_0(X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,X5))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X2,X3),X4),k3_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X5)))) )),
% 22.59/3.23    inference(superposition,[],[f161,f75])).
% 22.59/3.23  fof(f161,plain,(
% 22.59/3.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1)))) )),
% 22.59/3.23    inference(backward_demodulation,[],[f91,f152])).
% 22.59/3.23  fof(f152,plain,(
% 22.59/3.23    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 22.59/3.23    inference(superposition,[],[f75,f53])).
% 22.59/3.23  fof(f91,plain,(
% 22.59/3.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 22.59/3.23    inference(definition_unfolding,[],[f71,f58,f58])).
% 22.59/3.23  fof(f71,plain,(
% 22.59/3.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 22.59/3.23    inference(cnf_transformation,[],[f22])).
% 22.59/3.23  fof(f48,plain,(
% 22.59/3.23    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 22.59/3.23    inference(cnf_transformation,[],[f35])).
% 22.59/3.23  % SZS output end Proof for theBenchmark
% 22.59/3.23  % (31469)------------------------------
% 22.59/3.23  % (31469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 22.59/3.23  % (31469)Termination reason: Refutation
% 22.59/3.23  
% 22.59/3.23  % (31469)Memory used [KB]: 18805
% 22.59/3.23  % (31469)Time elapsed: 0.962 s
% 22.59/3.23  % (31469)------------------------------
% 22.59/3.23  % (31469)------------------------------
% 22.59/3.24  % (31193)Success in time 2.882 s
%------------------------------------------------------------------------------
