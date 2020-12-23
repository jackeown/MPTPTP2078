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
% DateTime   : Thu Dec  3 12:30:43 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   88 (1747 expanded)
%              Number of leaves         :   11 ( 547 expanded)
%              Depth                    :   27
%              Number of atoms          :  160 (2668 expanded)
%              Number of equality atoms :   73 (1619 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10828,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10777,f10773])).

fof(f10773,plain,(
    sP0(sK3,sK1,sK2) ),
    inference(subsumption_resolution,[],[f10771,f10057])).

fof(f10057,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f2896,f10018])).

fof(f10018,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f10000])).

fof(f10000,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | sK1 = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f6850,f9821])).

fof(f9821,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | sK1 = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f7208,f9767])).

fof(f9767,plain,
    ( sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | sK1 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f9708,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f9708,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)
    | sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f4059,f6855])).

fof(f6855,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f6745,f26])).

fof(f6745,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f4059,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f54,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f54,plain,
    ( r1_xboole_0(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(resolution,[],[f48,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X0)
        & r1_xboole_0(X1,X2)
        & ~ r1_xboole_0(X1,k2_xboole_0(X2,X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) )
      | ~ sP0(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) )
      | ~ sP0(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f48,plain,
    ( sP0(sK3,sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(resolution,[],[f36,f24])).

fof(f24,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | sP0(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
      & ( ~ r1_xboole_0(sK1,sK3)
        | ~ r1_xboole_0(sK1,sK2) ) )
    | sP0(sK3,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | sP0(X2,X0,X1) )
   => ( ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
        & ( ~ r1_xboole_0(sK1,sK3)
          | ~ r1_xboole_0(sK1,sK2) ) )
      | sP0(sK3,sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f12,f13])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f4059,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f3869,f26])).

fof(f3869,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0) ),
    inference(superposition,[],[f212,f179])).

fof(f179,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f164,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f164,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f76,f160])).

fof(f160,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f151,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f47,f26])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f36,f25])).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f151,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f76,f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f76,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f33,f49])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f212,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X17,X18))) = k4_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X17,k2_xboole_0(X18,X19))) ),
    inference(superposition,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f30,f30])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f7208,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) = X3 ),
    inference(superposition,[],[f6851,f29])).

fof(f6851,plain,(
    ! [X14,X12,X13] : k4_xboole_0(X12,k4_xboole_0(X13,k2_xboole_0(X14,X12))) = X12 ),
    inference(forward_demodulation,[],[f6741,f26])).

fof(f6741,plain,(
    ! [X14,X12,X13] : k4_xboole_0(X12,k4_xboole_0(X13,k2_xboole_0(X14,X12))) = k4_xboole_0(X12,k1_xboole_0) ),
    inference(superposition,[],[f4059,f4220])).

fof(f4220,plain,(
    ! [X118,X116,X117] : k1_xboole_0 = k4_xboole_0(X118,k4_xboole_0(X118,k4_xboole_0(X116,k2_xboole_0(X117,X118)))) ),
    inference(superposition,[],[f4051,f33])).

fof(f4051,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f3859,f49])).

fof(f3859,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f212,f27])).

fof(f6850,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X11,X10)) = X10 ),
    inference(forward_demodulation,[],[f6740,f26])).

fof(f6740,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k1_xboole_0) = k4_xboole_0(X10,k4_xboole_0(X11,X10)) ),
    inference(superposition,[],[f4059,f4051])).

fof(f2896,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(subsumption_resolution,[],[f2821,f81])).

fof(f81,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f33,f49])).

fof(f2821,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0)))
      | r1_xboole_0(k4_xboole_0(X1,X0),X0) ) ),
    inference(superposition,[],[f88,f27])).

fof(f88,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4))))
      | r1_xboole_0(k4_xboole_0(X2,X3),X4) ) ),
    inference(forward_demodulation,[],[f83,f33])).

fof(f83,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))
      | r1_xboole_0(k4_xboole_0(X2,X3),X4) ) ),
    inference(superposition,[],[f35,f33])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10771,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | sP0(sK3,sK1,sK2) ),
    inference(resolution,[],[f10726,f23])).

fof(f23,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ r1_xboole_0(sK1,sK2)
    | sP0(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f10726,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f10662])).

fof(f10662,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f35,f10545])).

fof(f10545,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f10433,f64])).

fof(f64,plain,
    ( ~ sP0(sK3,sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f60,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(trivial_inequality_removal,[],[f58])).

fof(f58,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f35,f56])).

fof(f56,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f53,f36])).

fof(f53,plain,
    ( r1_xboole_0(sK1,sK3)
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(resolution,[],[f48,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10433,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | sP0(sK3,sK1,sK2) ),
    inference(backward_demodulation,[],[f48,f10041])).

fof(f10041,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[],[f33,f10018])).

fof(f10777,plain,(
    ~ sP0(sK3,sK1,sK2) ),
    inference(superposition,[],[f10461,f10730])).

fof(f10730,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f10671,f26])).

fof(f10671,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f4059,f10545])).

fof(f10461,plain,(
    ! [X6] : ~ sP0(X6,k4_xboole_0(sK1,X6),sK2) ),
    inference(superposition,[],[f3013,f10041])).

fof(f3013,plain,(
    ! [X4,X5,X3] : ~ sP0(X3,k4_xboole_0(X4,k2_xboole_0(X5,X3)),X5) ),
    inference(resolution,[],[f2896,f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:26:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (16164)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (16157)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (16155)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (16156)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (16154)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (16163)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (16163)Refutation not found, incomplete strategy% (16163)------------------------------
% 0.22/0.49  % (16163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16163)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (16163)Memory used [KB]: 10618
% 0.22/0.49  % (16163)Time elapsed: 0.076 s
% 0.22/0.49  % (16163)------------------------------
% 0.22/0.49  % (16163)------------------------------
% 0.22/0.49  % (16162)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (16165)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (16169)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (16158)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (16168)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (16167)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (16159)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (16166)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (16153)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (16152)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.52  % (16160)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (16161)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 2.12/0.64  % (16164)Refutation found. Thanks to Tanya!
% 2.12/0.64  % SZS status Theorem for theBenchmark
% 2.12/0.64  % SZS output start Proof for theBenchmark
% 2.12/0.64  fof(f10828,plain,(
% 2.12/0.64    $false),
% 2.12/0.64    inference(subsumption_resolution,[],[f10777,f10773])).
% 2.12/0.64  fof(f10773,plain,(
% 2.12/0.64    sP0(sK3,sK1,sK2)),
% 2.12/0.64    inference(subsumption_resolution,[],[f10771,f10057])).
% 2.12/0.64  fof(f10057,plain,(
% 2.12/0.64    r1_xboole_0(sK1,sK2)),
% 2.12/0.64    inference(superposition,[],[f2896,f10018])).
% 2.12/0.64  fof(f10018,plain,(
% 2.12/0.64    sK1 = k4_xboole_0(sK1,sK2)),
% 2.12/0.64    inference(duplicate_literal_removal,[],[f10000])).
% 2.12/0.64  fof(f10000,plain,(
% 2.12/0.64    sK1 = k4_xboole_0(sK1,sK2) | sK1 = k4_xboole_0(sK1,sK2)),
% 2.12/0.64    inference(superposition,[],[f6850,f9821])).
% 2.12/0.64  fof(f9821,plain,(
% 2.12/0.64    sK2 = k4_xboole_0(sK2,sK1) | sK1 = k4_xboole_0(sK1,sK2)),
% 2.12/0.64    inference(superposition,[],[f7208,f9767])).
% 2.12/0.64  fof(f9767,plain,(
% 2.12/0.64    sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | sK1 = k4_xboole_0(sK1,sK2)),
% 2.12/0.64    inference(forward_demodulation,[],[f9708,f26])).
% 2.12/0.64  fof(f26,plain,(
% 2.12/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.12/0.64    inference(cnf_transformation,[],[f5])).
% 2.12/0.64  fof(f5,axiom,(
% 2.12/0.64    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.12/0.64  fof(f9708,plain,(
% 2.12/0.64    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) | sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))),
% 2.12/0.64    inference(superposition,[],[f4059,f6855])).
% 2.12/0.64  fof(f6855,plain,(
% 2.12/0.64    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))),
% 2.12/0.64    inference(forward_demodulation,[],[f6745,f26])).
% 2.12/0.64  fof(f6745,plain,(
% 2.12/0.64    k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.12/0.64    inference(superposition,[],[f4059,f57])).
% 2.12/0.64  fof(f57,plain,(
% 2.12/0.64    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.12/0.64    inference(resolution,[],[f54,f36])).
% 2.12/0.64  fof(f36,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.12/0.64    inference(definition_unfolding,[],[f31,f30])).
% 2.12/0.64  fof(f30,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f7])).
% 2.12/0.64  fof(f7,axiom,(
% 2.12/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.12/0.64  fof(f31,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f19])).
% 2.12/0.64  fof(f19,plain,(
% 2.12/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.12/0.64    inference(nnf_transformation,[],[f3])).
% 2.12/0.64  fof(f3,axiom,(
% 2.12/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.12/0.64  fof(f54,plain,(
% 2.12/0.64    r1_xboole_0(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 2.12/0.64    inference(resolution,[],[f48,f21])).
% 2.12/0.64  fof(f21,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_xboole_0(X1,X2)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f16])).
% 2.12/0.64  fof(f16,plain,(
% 2.12/0.64    ! [X0,X1,X2] : ((r1_xboole_0(X1,X0) & r1_xboole_0(X1,X2) & ~r1_xboole_0(X1,k2_xboole_0(X2,X0))) | ~sP0(X0,X1,X2))),
% 2.12/0.64    inference(rectify,[],[f15])).
% 2.12/0.64  fof(f15,plain,(
% 2.12/0.64    ! [X2,X0,X1] : ((r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) | ~sP0(X2,X0,X1))),
% 2.12/0.64    inference(nnf_transformation,[],[f13])).
% 2.12/0.64  fof(f13,plain,(
% 2.12/0.64    ! [X2,X0,X1] : ((r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) | ~sP0(X2,X0,X1))),
% 2.12/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.12/0.64  fof(f48,plain,(
% 2.12/0.64    sP0(sK3,sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 2.12/0.64    inference(resolution,[],[f36,f24])).
% 2.12/0.64  fof(f24,plain,(
% 2.12/0.64    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | sP0(sK3,sK1,sK2)),
% 2.12/0.64    inference(cnf_transformation,[],[f18])).
% 2.12/0.64  fof(f18,plain,(
% 2.12/0.64    (r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) & (~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2))) | sP0(sK3,sK1,sK2)),
% 2.12/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17])).
% 2.12/0.64  fof(f17,plain,(
% 2.12/0.64    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | sP0(X2,X0,X1)) => ((r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) & (~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2))) | sP0(sK3,sK1,sK2))),
% 2.12/0.64    introduced(choice_axiom,[])).
% 2.12/0.64  fof(f14,plain,(
% 2.12/0.64    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | sP0(X2,X0,X1))),
% 2.12/0.64    inference(definition_folding,[],[f12,f13])).
% 2.12/0.64  fof(f12,plain,(
% 2.12/0.64    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.12/0.64    inference(ennf_transformation,[],[f10])).
% 2.12/0.64  fof(f10,negated_conjecture,(
% 2.12/0.64    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.12/0.64    inference(negated_conjecture,[],[f9])).
% 2.12/0.64  fof(f9,conjecture,(
% 2.12/0.64    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.12/0.64  fof(f4059,plain,(
% 2.12/0.64    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 2.12/0.64    inference(forward_demodulation,[],[f3869,f26])).
% 2.12/0.64  fof(f3869,plain,(
% 2.12/0.64    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) )),
% 2.12/0.64    inference(superposition,[],[f212,f179])).
% 2.12/0.64  fof(f179,plain,(
% 2.12/0.64    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 2.12/0.64    inference(superposition,[],[f164,f29])).
% 2.12/0.64  fof(f29,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f1])).
% 2.12/0.64  fof(f1,axiom,(
% 2.12/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.12/0.64  fof(f164,plain,(
% 2.12/0.64    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 2.12/0.64    inference(backward_demodulation,[],[f76,f160])).
% 2.12/0.64  fof(f160,plain,(
% 2.12/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.12/0.64    inference(forward_demodulation,[],[f151,f49])).
% 2.12/0.64  fof(f49,plain,(
% 2.12/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.12/0.64    inference(forward_demodulation,[],[f47,f26])).
% 2.12/0.64  fof(f47,plain,(
% 2.12/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.12/0.64    inference(resolution,[],[f36,f25])).
% 2.12/0.64  fof(f25,plain,(
% 2.12/0.64    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f8])).
% 2.12/0.64  fof(f8,axiom,(
% 2.12/0.64    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.12/0.64  fof(f151,plain,(
% 2.12/0.64    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.12/0.64    inference(superposition,[],[f76,f27])).
% 2.12/0.64  fof(f27,plain,(
% 2.12/0.64    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.12/0.64    inference(cnf_transformation,[],[f11])).
% 2.12/0.64  fof(f11,plain,(
% 2.12/0.64    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.12/0.64    inference(rectify,[],[f4])).
% 2.12/0.64  fof(f4,axiom,(
% 2.12/0.64    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.12/0.64  fof(f76,plain,(
% 2.12/0.64    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 2.12/0.64    inference(superposition,[],[f33,f49])).
% 2.12/0.64  fof(f33,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f6])).
% 2.12/0.64  fof(f6,axiom,(
% 2.12/0.64    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.12/0.64  fof(f212,plain,(
% 2.12/0.64    ( ! [X19,X17,X18] : (k4_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X17,X18))) = k4_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X17,k2_xboole_0(X18,X19)))) )),
% 2.12/0.64    inference(superposition,[],[f34,f33])).
% 2.12/0.64  fof(f34,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.12/0.64    inference(definition_unfolding,[],[f28,f30,f30])).
% 2.12/0.64  fof(f28,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f2])).
% 2.12/0.64  fof(f2,axiom,(
% 2.12/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.12/0.64  fof(f7208,plain,(
% 2.12/0.64    ( ! [X4,X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) = X3) )),
% 2.12/0.64    inference(superposition,[],[f6851,f29])).
% 2.12/0.65  fof(f6851,plain,(
% 2.12/0.65    ( ! [X14,X12,X13] : (k4_xboole_0(X12,k4_xboole_0(X13,k2_xboole_0(X14,X12))) = X12) )),
% 2.12/0.65    inference(forward_demodulation,[],[f6741,f26])).
% 2.12/0.65  fof(f6741,plain,(
% 2.12/0.65    ( ! [X14,X12,X13] : (k4_xboole_0(X12,k4_xboole_0(X13,k2_xboole_0(X14,X12))) = k4_xboole_0(X12,k1_xboole_0)) )),
% 2.12/0.65    inference(superposition,[],[f4059,f4220])).
% 2.12/0.65  fof(f4220,plain,(
% 2.12/0.65    ( ! [X118,X116,X117] : (k1_xboole_0 = k4_xboole_0(X118,k4_xboole_0(X118,k4_xboole_0(X116,k2_xboole_0(X117,X118))))) )),
% 2.12/0.65    inference(superposition,[],[f4051,f33])).
% 2.12/0.65  fof(f4051,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 2.12/0.65    inference(forward_demodulation,[],[f3859,f49])).
% 2.12/0.65  fof(f3859,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) )),
% 2.12/0.65    inference(superposition,[],[f212,f27])).
% 2.12/0.65  fof(f6850,plain,(
% 2.12/0.65    ( ! [X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X11,X10)) = X10) )),
% 2.12/0.65    inference(forward_demodulation,[],[f6740,f26])).
% 2.12/0.65  fof(f6740,plain,(
% 2.12/0.65    ( ! [X10,X11] : (k4_xboole_0(X10,k1_xboole_0) = k4_xboole_0(X10,k4_xboole_0(X11,X10))) )),
% 2.12/0.65    inference(superposition,[],[f4059,f4051])).
% 2.12/0.65  fof(f2896,plain,(
% 2.12/0.65    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 2.12/0.65    inference(subsumption_resolution,[],[f2821,f81])).
% 2.12/0.65  fof(f81,plain,(
% 2.12/0.65    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 2.12/0.65    inference(superposition,[],[f33,f49])).
% 2.12/0.65  fof(f2821,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) | r1_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 2.12/0.65    inference(superposition,[],[f88,f27])).
% 2.12/0.65  fof(f88,plain,(
% 2.12/0.65    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) | r1_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 2.12/0.65    inference(forward_demodulation,[],[f83,f33])).
% 2.12/0.65  fof(f83,plain,(
% 2.12/0.65    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4))) | r1_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 2.12/0.65    inference(superposition,[],[f35,f33])).
% 2.12/0.65  fof(f35,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.12/0.65    inference(definition_unfolding,[],[f32,f30])).
% 2.12/0.65  fof(f32,plain,(
% 2.12/0.65    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.12/0.65    inference(cnf_transformation,[],[f19])).
% 2.12/0.65  fof(f10771,plain,(
% 2.12/0.65    ~r1_xboole_0(sK1,sK2) | sP0(sK3,sK1,sK2)),
% 2.12/0.65    inference(resolution,[],[f10726,f23])).
% 2.12/0.65  fof(f23,plain,(
% 2.12/0.65    ~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2) | sP0(sK3,sK1,sK2)),
% 2.12/0.65    inference(cnf_transformation,[],[f18])).
% 2.12/0.65  fof(f10726,plain,(
% 2.12/0.65    r1_xboole_0(sK1,sK3)),
% 2.12/0.65    inference(trivial_inequality_removal,[],[f10662])).
% 2.12/0.65  fof(f10662,plain,(
% 2.12/0.65    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK3)),
% 2.12/0.65    inference(superposition,[],[f35,f10545])).
% 2.12/0.65  fof(f10545,plain,(
% 2.12/0.65    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 2.12/0.65    inference(subsumption_resolution,[],[f10433,f64])).
% 2.12/0.65  fof(f64,plain,(
% 2.12/0.65    ~sP0(sK3,sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 2.12/0.65    inference(resolution,[],[f60,f20])).
% 2.12/0.65  fof(f20,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k2_xboole_0(X2,X0)) | ~sP0(X0,X1,X2)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f16])).
% 2.12/0.65  fof(f60,plain,(
% 2.12/0.65    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 2.12/0.65    inference(trivial_inequality_removal,[],[f58])).
% 2.12/0.65  fof(f58,plain,(
% 2.12/0.65    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 2.12/0.65    inference(superposition,[],[f35,f56])).
% 2.12/0.65  fof(f56,plain,(
% 2.12/0.65    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 2.12/0.65    inference(resolution,[],[f53,f36])).
% 2.12/0.65  fof(f53,plain,(
% 2.12/0.65    r1_xboole_0(sK1,sK3) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 2.12/0.65    inference(resolution,[],[f48,f22])).
% 2.12/0.65  fof(f22,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_xboole_0(X1,X0)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f16])).
% 2.12/0.65  fof(f10433,plain,(
% 2.12/0.65    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | sP0(sK3,sK1,sK2)),
% 2.12/0.65    inference(backward_demodulation,[],[f48,f10041])).
% 2.12/0.65  fof(f10041,plain,(
% 2.12/0.65    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK1,X0)) )),
% 2.12/0.65    inference(superposition,[],[f33,f10018])).
% 2.12/0.65  fof(f10777,plain,(
% 2.12/0.65    ~sP0(sK3,sK1,sK2)),
% 2.12/0.65    inference(superposition,[],[f10461,f10730])).
% 2.12/0.65  fof(f10730,plain,(
% 2.12/0.65    sK1 = k4_xboole_0(sK1,sK3)),
% 2.12/0.65    inference(forward_demodulation,[],[f10671,f26])).
% 2.12/0.65  fof(f10671,plain,(
% 2.12/0.65    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 2.12/0.65    inference(superposition,[],[f4059,f10545])).
% 2.12/0.65  fof(f10461,plain,(
% 2.12/0.65    ( ! [X6] : (~sP0(X6,k4_xboole_0(sK1,X6),sK2)) )),
% 2.12/0.65    inference(superposition,[],[f3013,f10041])).
% 2.12/0.65  fof(f3013,plain,(
% 2.12/0.65    ( ! [X4,X5,X3] : (~sP0(X3,k4_xboole_0(X4,k2_xboole_0(X5,X3)),X5)) )),
% 2.12/0.65    inference(resolution,[],[f2896,f20])).
% 2.12/0.65  % SZS output end Proof for theBenchmark
% 2.12/0.65  % (16164)------------------------------
% 2.12/0.65  % (16164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.65  % (16164)Termination reason: Refutation
% 2.12/0.65  
% 2.12/0.65  % (16164)Memory used [KB]: 6780
% 2.12/0.65  % (16164)Time elapsed: 0.229 s
% 2.12/0.65  % (16164)------------------------------
% 2.12/0.65  % (16164)------------------------------
% 2.12/0.65  % (16151)Success in time 0.285 s
%------------------------------------------------------------------------------
