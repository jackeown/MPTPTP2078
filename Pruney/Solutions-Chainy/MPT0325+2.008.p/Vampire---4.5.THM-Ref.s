%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:38 EST 2020

% Result     : Theorem 25.11s
% Output     : Refutation 25.11s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 540 expanded)
%              Number of leaves         :   22 ( 167 expanded)
%              Depth                    :   31
%              Number of atoms          :  254 ( 892 expanded)
%              Number of equality atoms :  146 ( 545 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69801,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f30859,f32801,f51859,f64309,f64598,f69754])).

fof(f69754,plain,
    ( spl4_1
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f69753])).

fof(f69753,plain,
    ( $false
    | spl4_1
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f69693,f52])).

fof(f52,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f69693,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_9 ),
    inference(superposition,[],[f67,f69567])).

fof(f69567,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f69566,f29])).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f69566,plain,
    ( k3_xboole_0(sK0,sK2) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f69494,f152])).

fof(f152,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f138,f59])).

fof(f59,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f138,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f39,f28])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f69494,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK2)))
    | ~ spl4_9 ),
    inference(superposition,[],[f350,f69212])).

fof(f69212,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK2),sK0)
    | ~ spl4_9 ),
    inference(superposition,[],[f65143,f95])).

fof(f95,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f74,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f74,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3) ),
    inference(resolution,[],[f35,f67])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f65143,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK2),X0))
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f65084,f360])).

fof(f360,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f339,f28])).

fof(f339,plain,(
    ! [X4,X3] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X3,X3),X4) ),
    inference(superposition,[],[f41,f28])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f65084,plain,
    ( ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK2),X0))
    | ~ spl4_9 ),
    inference(superposition,[],[f40,f64304])).

fof(f64304,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f64302])).

fof(f64302,plain,
    ( spl4_9
  <=> k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f350,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f317,f33])).

fof(f317,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f41,f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f67,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f31,f33])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f64598,plain,(
    ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f64597])).

fof(f64597,plain,
    ( $false
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f64448,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f64448,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f26,f64308])).

fof(f64308,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f64306])).

fof(f64306,plain,
    ( spl4_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f26,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f21])).

fof(f21,plain,
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

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f64309,plain,
    ( spl4_9
    | spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f64300,f54,f64306,f64302])).

fof(f54,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f64300,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f64299,f51933])).

fof(f51933,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f55,f35])).

fof(f55,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f64299,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2))
    | k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f64216])).

fof(f64216,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2))
    | k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl4_2 ),
    inference(superposition,[],[f586,f52700])).

fof(f52700,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,sK2),sK3))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f52699,f28])).

fof(f52699,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,sK2),sK3))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f52640,f51933])).

fof(f52640,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,sK2),sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f27189,f72])).

fof(f72,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f35,f25])).

fof(f25,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f27189,plain,(
    ! [X10,X8,X11,X9] : k5_xboole_0(k2_zfmisc_1(X8,k3_xboole_0(X10,X11)),k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11))) = k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(k5_xboole_0(X8,X9),X11)) ),
    inference(forward_demodulation,[],[f27072,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f27072,plain,(
    ! [X10,X8,X11,X9] : k2_zfmisc_1(k3_xboole_0(X8,k5_xboole_0(X8,X9)),k3_xboole_0(X10,X11)) = k5_xboole_0(k2_zfmisc_1(X8,k3_xboole_0(X10,X11)),k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11))) ),
    inference(superposition,[],[f26626,f44])).

fof(f26626,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2)) = k2_zfmisc_1(k3_xboole_0(X0,k5_xboole_0(X0,X1)),X2) ),
    inference(backward_demodulation,[],[f17550,f26236])).

fof(f26236,plain,(
    ! [X4,X2,X3] : k2_zfmisc_1(k5_xboole_0(X2,k3_xboole_0(X2,X4)),X3) = k2_zfmisc_1(k3_xboole_0(X2,k5_xboole_0(X2,X4)),X3) ),
    inference(forward_demodulation,[],[f26235,f18135])).

fof(f18135,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(k3_xboole_0(X3,X2),X4)) = k2_zfmisc_1(k3_xboole_0(X2,k5_xboole_0(X2,X3)),X4) ),
    inference(forward_demodulation,[],[f18074,f350])).

fof(f18074,plain,(
    ! [X4,X2,X3] : k2_zfmisc_1(k5_xboole_0(X2,k3_xboole_0(X3,X2)),X4) = k5_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(k3_xboole_0(X3,X2),X4)) ),
    inference(superposition,[],[f17550,f33])).

fof(f26235,plain,(
    ! [X4,X2,X3] : k2_zfmisc_1(k5_xboole_0(X2,k3_xboole_0(X2,X4)),X3) = k5_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(k3_xboole_0(X4,X2),X3)) ),
    inference(forward_demodulation,[],[f1453,f571])).

fof(f571,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f44,f30])).

fof(f1453,plain,(
    ! [X4,X2,X3] : k2_zfmisc_1(k5_xboole_0(X2,k3_xboole_0(X2,X4)),X3) = k5_xboole_0(k2_zfmisc_1(X2,X3),k3_xboole_0(k2_zfmisc_1(X4,X3),k2_zfmisc_1(X2,X3))) ),
    inference(superposition,[],[f46,f33])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f42,f34,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f17550,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f46,f571])).

fof(f586,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | k3_xboole_0(X0,X1) = k1_xboole_0
      | k1_xboole_0 = k3_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f36,f44])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51859,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f51858])).

fof(f51858,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f51822,f48])).

fof(f48,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51822,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f26,f30858])).

fof(f30858,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f30856])).

fof(f30856,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f32801,plain,
    ( spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f32800])).

fof(f32800,plain,
    ( $false
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f32702,f56])).

fof(f56,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f32702,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl4_3 ),
    inference(superposition,[],[f67,f32465])).

fof(f32465,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f32464,f152])).

fof(f32464,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK3)))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f32252,f29])).

fof(f32252,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK3))) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_3 ),
    inference(superposition,[],[f350,f31425])).

fof(f31425,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK3),sK1)
    | ~ spl4_3 ),
    inference(superposition,[],[f31185,f95])).

fof(f31185,plain,
    ( ! [X55] : k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK3),X55))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f30980,f360])).

fof(f30980,plain,
    ( ! [X55] : k3_xboole_0(k1_xboole_0,X55) = k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK3),X55))
    | ~ spl4_3 ),
    inference(superposition,[],[f40,f30854])).

fof(f30854,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK1,sK3))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f30852])).

fof(f30852,plain,
    ( spl4_3
  <=> k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f30859,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f30742,f30856,f30852])).

fof(f30742,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK1,sK3)) ),
    inference(trivial_inequality_removal,[],[f30715])).

fof(f30715,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f36,f30605])).

fof(f30605,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k5_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f30549,f28])).

fof(f30549,plain,(
    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k5_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f24795,f30337])).

fof(f30337,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f30151,f83])).

fof(f83,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f73,f33])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f35,f31])).

fof(f30151,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f27016,f556])).

fof(f556,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f44,f30])).

fof(f27016,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(resolution,[],[f26988,f35])).

fof(f26988,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f22698,f120])).

fof(f120,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f95,f72])).

fof(f22698,plain,(
    ! [X19,X18] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X18,X19),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X19))) ),
    inference(forward_demodulation,[],[f22685,f44])).

fof(f22685,plain,(
    ! [X19,X18] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X18,sK0),k3_xboole_0(X19,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X19))) ),
    inference(superposition,[],[f17026,f571])).

fof(f17026,plain,(
    ! [X149,X150] : r1_tarski(k3_xboole_0(X150,k2_zfmisc_1(sK0,k3_xboole_0(X149,sK1))),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X149))) ),
    inference(forward_demodulation,[],[f16829,f556])).

fof(f16829,plain,(
    ! [X149,X150] : r1_tarski(k3_xboole_0(X150,k3_xboole_0(k2_zfmisc_1(sK0,X149),k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X149))) ),
    inference(superposition,[],[f5546,f556])).

fof(f5546,plain,(
    ! [X4,X3] : r1_tarski(k3_xboole_0(X4,k3_xboole_0(X3,k2_zfmisc_1(sK0,sK1))),k3_xboole_0(k2_zfmisc_1(sK0,sK1),X3)) ),
    inference(forward_demodulation,[],[f5545,f267])).

fof(f267,plain,(
    ! [X0] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),X0) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X0,k2_zfmisc_1(sK2,sK3))) ),
    inference(superposition,[],[f232,f33])).

fof(f232,plain,(
    ! [X14] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X14)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),X14) ),
    inference(superposition,[],[f40,f72])).

fof(f5545,plain,(
    ! [X4,X3] : r1_tarski(k3_xboole_0(X4,k3_xboole_0(X3,k2_zfmisc_1(sK0,sK1))),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X3,k2_zfmisc_1(sK2,sK3)))) ),
    inference(forward_demodulation,[],[f5510,f33])).

fof(f5510,plain,(
    ! [X4,X3] : r1_tarski(k3_xboole_0(X4,k3_xboole_0(X3,k2_zfmisc_1(sK0,sK1))),k3_xboole_0(k3_xboole_0(X3,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f5451,f4884])).

fof(f4884,plain,(
    ! [X10] : k3_xboole_0(X10,k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X10,k2_zfmisc_1(sK2,sK3))) ),
    inference(superposition,[],[f228,f1078])).

fof(f1078,plain,(
    ! [X26] : k3_xboole_0(X26,k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k3_xboole_0(X26,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK3)) ),
    inference(superposition,[],[f73,f519])).

fof(f519,plain,(
    ! [X2] : k3_xboole_0(X2,k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(X2,k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f233,f33])).

fof(f233,plain,(
    ! [X15] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),X15) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK0,sK1),X15)) ),
    inference(superposition,[],[f40,f120])).

fof(f228,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(k3_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f40,f33])).

fof(f5451,plain,(
    ! [X4,X3] : r1_tarski(k3_xboole_0(X4,k3_xboole_0(k2_zfmisc_1(sK0,sK1),X3)),k3_xboole_0(X3,k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f5428,f40])).

fof(f5428,plain,(
    ! [X4,X3] : r1_tarski(k3_xboole_0(k3_xboole_0(X4,k2_zfmisc_1(sK0,sK1)),X3),k3_xboole_0(X3,k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f5270,f33])).

fof(f5270,plain,(
    ! [X109,X108] : r1_tarski(k3_xboole_0(X109,k3_xboole_0(X108,k2_zfmisc_1(sK0,sK1))),k3_xboole_0(X109,k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f247,f4884])).

fof(f247,plain,(
    ! [X6,X8,X7] : r1_tarski(k3_xboole_0(X6,k3_xboole_0(X7,X8)),k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f31,f40])).

fof(f24795,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1))) = k2_zfmisc_1(X2,k3_xboole_0(X0,k5_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f16748,f24550])).

fof(f24550,plain,(
    ! [X4,X2,X3] : k2_zfmisc_1(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4))) = k2_zfmisc_1(X2,k3_xboole_0(X3,k5_xboole_0(X3,X4))) ),
    inference(forward_demodulation,[],[f24549,f17335])).

fof(f17335,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,k3_xboole_0(X3,X2))) = k2_zfmisc_1(X4,k3_xboole_0(X2,k5_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f17275,f350])).

fof(f17275,plain,(
    ! [X4,X2,X3] : k2_zfmisc_1(X4,k5_xboole_0(X2,k3_xboole_0(X3,X2))) = k5_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,k3_xboole_0(X3,X2))) ),
    inference(superposition,[],[f16748,f33])).

fof(f24549,plain,(
    ! [X4,X2,X3] : k2_zfmisc_1(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4))) = k5_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X2,k3_xboole_0(X4,X3))) ),
    inference(forward_demodulation,[],[f842,f556])).

fof(f842,plain,(
    ! [X4,X2,X3] : k2_zfmisc_1(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4))) = k5_xboole_0(k2_zfmisc_1(X2,X3),k3_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X2,X3))) ),
    inference(superposition,[],[f45,f33])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f43,f34,f34])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f16748,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f45,f556])).

fof(f57,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f27,f54,f50])).

fof(f27,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:31:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (27896)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (27881)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (27888)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (27897)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (27898)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (27889)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (27904)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (27882)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (27891)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (27899)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (27892)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (27876)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (27900)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.54  % (27883)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.54  % (27879)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.55  % (27901)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.55  % (27884)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.55  % (27890)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.55  % (27895)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.55  % (27893)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.55  % (27877)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.55  % (27898)Refutation not found, incomplete strategy% (27898)------------------------------
% 1.29/0.55  % (27898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (27898)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (27898)Memory used [KB]: 10746
% 1.29/0.55  % (27898)Time elapsed: 0.139 s
% 1.29/0.55  % (27898)------------------------------
% 1.29/0.55  % (27898)------------------------------
% 1.29/0.55  % (27887)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.55  % (27880)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.56  % (27878)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.56  % (27885)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  % (27886)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.56  % (27903)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.56  % (27902)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.57  % (27894)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.57  % (27893)Refutation not found, incomplete strategy% (27893)------------------------------
% 1.50/0.57  % (27893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (27893)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (27893)Memory used [KB]: 10618
% 1.50/0.57  % (27893)Time elapsed: 0.158 s
% 1.50/0.57  % (27893)------------------------------
% 1.50/0.57  % (27893)------------------------------
% 1.50/0.57  % (27905)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.37/0.70  % (27907)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.37/0.72  % (27906)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.70/0.86  % (27881)Time limit reached!
% 3.70/0.86  % (27881)------------------------------
% 3.70/0.86  % (27881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.70/0.87  % (27881)Termination reason: Time limit
% 3.70/0.87  % (27881)Termination phase: Saturation
% 3.70/0.87  
% 3.70/0.87  % (27881)Memory used [KB]: 10490
% 3.70/0.87  % (27881)Time elapsed: 0.400 s
% 3.70/0.87  % (27881)------------------------------
% 3.70/0.87  % (27881)------------------------------
% 3.70/0.92  % (27876)Time limit reached!
% 3.70/0.92  % (27876)------------------------------
% 3.70/0.92  % (27876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.70/0.92  % (27876)Termination reason: Time limit
% 3.70/0.92  
% 3.70/0.92  % (27876)Memory used [KB]: 3965
% 3.70/0.92  % (27876)Time elapsed: 0.504 s
% 3.70/0.92  % (27876)------------------------------
% 3.70/0.92  % (27876)------------------------------
% 3.70/0.92  % (27888)Time limit reached!
% 3.70/0.92  % (27888)------------------------------
% 3.70/0.92  % (27888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.70/0.92  % (27886)Time limit reached!
% 3.70/0.92  % (27886)------------------------------
% 3.70/0.92  % (27886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.70/0.92  % (27886)Termination reason: Time limit
% 3.70/0.92  
% 3.70/0.92  % (27886)Memory used [KB]: 16886
% 3.70/0.92  % (27886)Time elapsed: 0.506 s
% 3.70/0.92  % (27886)------------------------------
% 3.70/0.92  % (27886)------------------------------
% 3.70/0.92  % (27888)Termination reason: Time limit
% 3.70/0.92  % (27888)Termination phase: Saturation
% 3.70/0.92  
% 3.70/0.92  % (27888)Memory used [KB]: 11257
% 3.70/0.92  % (27888)Time elapsed: 0.500 s
% 3.70/0.92  % (27888)------------------------------
% 3.70/0.92  % (27888)------------------------------
% 4.30/0.95  % (27877)Time limit reached!
% 4.30/0.95  % (27877)------------------------------
% 4.30/0.95  % (27877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/0.95  % (27877)Termination reason: Time limit
% 4.30/0.95  
% 4.30/0.95  % (27877)Memory used [KB]: 9850
% 4.30/0.95  % (27877)Time elapsed: 0.525 s
% 4.30/0.95  % (27877)------------------------------
% 4.30/0.95  % (27877)------------------------------
% 4.56/1.01  % (27908)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.56/1.01  % (27904)Time limit reached!
% 4.56/1.01  % (27904)------------------------------
% 4.56/1.01  % (27904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.56/1.01  % (27904)Termination reason: Time limit
% 4.56/1.01  % (27904)Termination phase: Saturation
% 4.56/1.01  
% 4.56/1.01  % (27904)Memory used [KB]: 11129
% 4.56/1.01  % (27904)Time elapsed: 0.600 s
% 4.56/1.01  % (27904)------------------------------
% 4.56/1.01  % (27904)------------------------------
% 4.56/1.02  % (27892)Time limit reached!
% 4.56/1.02  % (27892)------------------------------
% 4.56/1.02  % (27892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.56/1.02  % (27892)Termination reason: Time limit
% 4.56/1.02  % (27892)Termination phase: Saturation
% 4.56/1.02  
% 4.56/1.02  % (27892)Memory used [KB]: 17142
% 4.56/1.02  % (27892)Time elapsed: 0.600 s
% 4.56/1.02  % (27892)------------------------------
% 4.56/1.02  % (27892)------------------------------
% 4.56/1.03  % (27910)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.92/1.04  % (27909)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.92/1.04  % (27911)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.47/1.08  % (27883)Time limit reached!
% 5.47/1.08  % (27883)------------------------------
% 5.47/1.08  % (27883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.47/1.08  % (27883)Termination reason: Time limit
% 5.47/1.08  
% 5.47/1.08  % (27883)Memory used [KB]: 12920
% 5.47/1.08  % (27883)Time elapsed: 0.626 s
% 5.47/1.08  % (27883)------------------------------
% 5.47/1.08  % (27883)------------------------------
% 5.47/1.09  % (27912)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.97/1.14  % (27913)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.27/1.18  % (27914)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.27/1.22  % (27915)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.27/1.23  % (27897)Time limit reached!
% 6.27/1.23  % (27897)------------------------------
% 6.27/1.23  % (27897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.27/1.23  % (27897)Termination reason: Time limit
% 6.27/1.23  % (27897)Termination phase: Saturation
% 6.27/1.23  
% 6.27/1.23  % (27897)Memory used [KB]: 8571
% 6.27/1.23  % (27897)Time elapsed: 0.800 s
% 6.27/1.23  % (27897)------------------------------
% 6.27/1.23  % (27897)------------------------------
% 7.47/1.35  % (27916)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.74/1.37  % (27909)Time limit reached!
% 7.74/1.37  % (27909)------------------------------
% 7.74/1.37  % (27909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.74/1.37  % (27909)Termination reason: Time limit
% 7.74/1.37  % (27909)Termination phase: Saturation
% 7.74/1.37  
% 7.74/1.37  % (27909)Memory used [KB]: 8443
% 7.74/1.37  % (27909)Time elapsed: 0.400 s
% 7.74/1.37  % (27909)------------------------------
% 7.74/1.37  % (27909)------------------------------
% 7.74/1.38  % (27910)Time limit reached!
% 7.74/1.38  % (27910)------------------------------
% 7.74/1.38  % (27910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.74/1.38  % (27910)Termination reason: Time limit
% 7.74/1.38  % (27910)Termination phase: Saturation
% 7.74/1.38  
% 7.74/1.38  % (27910)Memory used [KB]: 15735
% 7.74/1.38  % (27910)Time elapsed: 0.400 s
% 7.74/1.38  % (27910)------------------------------
% 7.74/1.38  % (27910)------------------------------
% 7.74/1.42  % (27878)Time limit reached!
% 7.74/1.42  % (27878)------------------------------
% 7.74/1.42  % (27878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.24/1.43  % (27878)Termination reason: Time limit
% 8.24/1.43  % (27878)Termination phase: Saturation
% 8.24/1.43  
% 8.24/1.43  % (27878)Memory used [KB]: 21748
% 8.24/1.43  % (27878)Time elapsed: 1.0000 s
% 8.24/1.43  % (27878)------------------------------
% 8.24/1.43  % (27878)------------------------------
% 8.50/1.50  % (27917)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.50/1.51  % (27918)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 8.50/1.53  % (27919)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.14/1.63  % (27902)Time limit reached!
% 9.14/1.63  % (27902)------------------------------
% 9.14/1.63  % (27902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.14/1.63  % (27902)Termination reason: Time limit
% 9.14/1.63  % (27902)Termination phase: Saturation
% 9.14/1.63  
% 9.14/1.63  % (27902)Memory used [KB]: 20084
% 9.14/1.63  % (27902)Time elapsed: 1.200 s
% 9.14/1.63  % (27902)------------------------------
% 9.14/1.63  % (27902)------------------------------
% 10.26/1.73  % (27900)Time limit reached!
% 10.26/1.73  % (27900)------------------------------
% 10.26/1.73  % (27900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.26/1.73  % (27900)Termination reason: Time limit
% 10.26/1.73  
% 10.26/1.73  % (27900)Memory used [KB]: 20340
% 10.26/1.73  % (27900)Time elapsed: 1.309 s
% 10.26/1.73  % (27900)------------------------------
% 10.26/1.73  % (27900)------------------------------
% 10.80/1.77  % (27891)Time limit reached!
% 10.80/1.77  % (27891)------------------------------
% 10.80/1.77  % (27891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.80/1.77  % (27891)Termination reason: Time limit
% 10.80/1.77  % (27891)Termination phase: Saturation
% 10.80/1.77  
% 10.80/1.77  % (27891)Memory used [KB]: 17782
% 10.80/1.77  % (27891)Time elapsed: 1.313 s
% 10.80/1.77  % (27891)------------------------------
% 10.80/1.77  % (27891)------------------------------
% 11.02/1.78  % (27920)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.46/1.85  % (27921)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.65/1.90  % (27922)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 12.12/1.93  % (27918)Time limit reached!
% 12.12/1.93  % (27918)------------------------------
% 12.12/1.93  % (27918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.12/1.93  % (27918)Termination reason: Time limit
% 12.12/1.93  
% 12.12/1.93  % (27918)Memory used [KB]: 4477
% 12.12/1.93  % (27918)Time elapsed: 0.514 s
% 12.12/1.93  % (27918)------------------------------
% 12.12/1.93  % (27918)------------------------------
% 12.12/1.94  % (27880)Time limit reached!
% 12.12/1.94  % (27880)------------------------------
% 12.12/1.94  % (27880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.12/1.95  % (27880)Termination reason: Time limit
% 12.12/1.95  
% 12.12/1.95  % (27880)Memory used [KB]: 20084
% 12.12/1.95  % (27880)Time elapsed: 1.510 s
% 12.12/1.95  % (27880)------------------------------
% 12.12/1.95  % (27880)------------------------------
% 12.12/1.95  % (27903)Time limit reached!
% 12.12/1.95  % (27903)------------------------------
% 12.12/1.95  % (27903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.12/1.95  % (27903)Termination reason: Time limit
% 12.12/1.95  
% 12.12/1.95  % (27903)Memory used [KB]: 17398
% 12.12/1.95  % (27903)Time elapsed: 1.534 s
% 12.12/1.95  % (27903)------------------------------
% 12.12/1.95  % (27903)------------------------------
% 12.49/2.03  % (27887)Time limit reached!
% 12.49/2.03  % (27887)------------------------------
% 12.49/2.03  % (27887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.97/2.04  % (27887)Termination reason: Time limit
% 12.97/2.04  
% 12.97/2.04  % (27887)Memory used [KB]: 21492
% 12.97/2.04  % (27887)Time elapsed: 1.621 s
% 12.97/2.04  % (27887)------------------------------
% 12.97/2.04  % (27887)------------------------------
% 12.97/2.05  % (27924)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.14/2.07  % (27923)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 13.14/2.09  % (27925)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 14.22/2.17  % (27926)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 14.22/2.18  % (27912)Time limit reached!
% 14.22/2.18  % (27912)------------------------------
% 14.22/2.18  % (27912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.22/2.19  % (27912)Termination reason: Time limit
% 14.22/2.19  % (27912)Termination phase: Saturation
% 14.22/2.19  
% 14.22/2.19  % (27912)Memory used [KB]: 19445
% 14.22/2.19  % (27912)Time elapsed: 1.200 s
% 14.22/2.19  % (27912)------------------------------
% 14.22/2.19  % (27912)------------------------------
% 14.22/2.20  % (27922)Time limit reached!
% 14.22/2.20  % (27922)------------------------------
% 14.22/2.20  % (27922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.22/2.20  % (27922)Termination reason: Time limit
% 14.22/2.20  
% 14.22/2.20  % (27922)Memory used [KB]: 4605
% 14.22/2.20  % (27922)Time elapsed: 0.410 s
% 14.22/2.20  % (27922)------------------------------
% 14.22/2.20  % (27922)------------------------------
% 14.22/2.23  % (27890)Time limit reached!
% 14.22/2.23  % (27890)------------------------------
% 14.22/2.23  % (27890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.22/2.23  % (27890)Termination reason: Time limit
% 14.22/2.23  
% 14.22/2.23  % (27890)Memory used [KB]: 14839
% 14.22/2.23  % (27890)Time elapsed: 1.822 s
% 14.22/2.23  % (27890)------------------------------
% 14.22/2.23  % (27890)------------------------------
% 15.09/2.30  % (27927)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.09/2.33  % (27928)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.09/2.33  % (27929)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 15.67/2.37  % (27925)Time limit reached!
% 15.67/2.37  % (27925)------------------------------
% 15.67/2.37  % (27925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.67/2.37  % (27925)Termination reason: Time limit
% 15.67/2.37  
% 15.67/2.37  % (27925)Memory used [KB]: 3582
% 15.67/2.37  % (27925)Time elapsed: 0.404 s
% 15.67/2.37  % (27925)------------------------------
% 15.67/2.37  % (27925)------------------------------
% 16.36/2.46  % (27894)Time limit reached!
% 16.36/2.46  % (27894)------------------------------
% 16.36/2.46  % (27894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.36/2.47  % (27894)Termination reason: Time limit
% 16.36/2.47  
% 16.36/2.47  % (27894)Memory used [KB]: 27376
% 16.36/2.47  % (27894)Time elapsed: 2.022 s
% 16.36/2.47  % (27894)------------------------------
% 16.36/2.47  % (27894)------------------------------
% 16.36/2.47  % (27930)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.36/2.47  % (27882)Time limit reached!
% 16.36/2.47  % (27882)------------------------------
% 16.36/2.47  % (27882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.36/2.47  % (27882)Termination reason: Time limit
% 16.36/2.47  
% 16.36/2.47  % (27882)Memory used [KB]: 28272
% 16.36/2.47  % (27882)Time elapsed: 2.054 s
% 16.36/2.47  % (27882)------------------------------
% 16.36/2.47  % (27882)------------------------------
% 17.15/2.59  % (27932)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.15/2.61  % (27931)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 17.15/2.61  % (27908)Time limit reached!
% 17.15/2.61  % (27908)------------------------------
% 17.15/2.61  % (27908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.15/2.61  % (27908)Termination reason: Time limit
% 17.15/2.61  
% 17.15/2.61  % (27908)Memory used [KB]: 23922
% 17.15/2.61  % (27908)Time elapsed: 1.710 s
% 17.15/2.61  % (27908)------------------------------
% 17.15/2.61  % (27908)------------------------------
% 18.69/2.75  % (27933)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 18.98/2.83  % (27914)Time limit reached!
% 18.98/2.83  % (27914)------------------------------
% 18.98/2.83  % (27914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.98/2.83  % (27914)Termination reason: Time limit
% 18.98/2.83  
% 18.98/2.83  % (27914)Memory used [KB]: 18677
% 18.98/2.83  % (27914)Time elapsed: 1.731 s
% 18.98/2.83  % (27914)------------------------------
% 18.98/2.83  % (27914)------------------------------
% 18.98/2.83  % (27930)Time limit reached!
% 18.98/2.83  % (27930)------------------------------
% 18.98/2.83  % (27930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.98/2.83  % (27930)Termination reason: Time limit
% 18.98/2.83  % (27930)Termination phase: Saturation
% 18.98/2.83  
% 18.98/2.83  % (27930)Memory used [KB]: 12153
% 18.98/2.83  % (27930)Time elapsed: 0.400 s
% 18.98/2.83  % (27930)------------------------------
% 18.98/2.83  % (27930)------------------------------
% 20.43/2.95  % (27884)Time limit reached!
% 20.43/2.95  % (27884)------------------------------
% 20.43/2.95  % (27884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.43/2.95  % (27884)Termination reason: Time limit
% 20.43/2.95  % (27884)Termination phase: Saturation
% 20.43/2.95  
% 20.43/2.95  % (27884)Memory used [KB]: 45926
% 20.43/2.95  % (27884)Time elapsed: 2.537 s
% 20.43/2.95  % (27884)------------------------------
% 20.43/2.95  % (27884)------------------------------
% 20.43/2.95  % (27932)Time limit reached!
% 20.43/2.95  % (27932)------------------------------
% 20.43/2.95  % (27932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.43/2.95  % (27932)Termination reason: Time limit
% 20.43/2.95  % (27932)Termination phase: Saturation
% 20.43/2.95  
% 20.43/2.95  % (27932)Memory used [KB]: 13304
% 20.43/2.95  % (27932)Time elapsed: 0.400 s
% 20.43/2.95  % (27932)------------------------------
% 20.43/2.95  % (27932)------------------------------
% 20.43/2.97  % (27921)Time limit reached!
% 20.43/2.97  % (27921)------------------------------
% 20.43/2.97  % (27921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.43/2.97  % (27921)Termination reason: Time limit
% 20.43/2.97  
% 20.43/2.97  % (27921)Memory used [KB]: 15735
% 20.43/2.97  % (27921)Time elapsed: 1.203 s
% 20.43/2.97  % (27921)------------------------------
% 20.43/2.97  % (27921)------------------------------
% 21.03/3.03  % (27895)Time limit reached!
% 21.03/3.03  % (27895)------------------------------
% 21.03/3.03  % (27895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.03/3.03  % (27895)Termination reason: Time limit
% 21.03/3.03  % (27895)Termination phase: Saturation
% 21.03/3.03  
% 21.03/3.03  % (27895)Memory used [KB]: 41449
% 21.03/3.03  % (27895)Time elapsed: 2.600 s
% 21.03/3.03  % (27895)------------------------------
% 21.03/3.03  % (27895)------------------------------
% 22.96/3.31  % (27924)Time limit reached!
% 22.96/3.31  % (27924)------------------------------
% 22.96/3.31  % (27924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.51/3.33  % (27924)Termination reason: Time limit
% 23.51/3.33  % (27924)Termination phase: Saturation
% 23.51/3.33  
% 23.51/3.33  % (27924)Memory used [KB]: 17398
% 23.51/3.33  % (27924)Time elapsed: 1.300 s
% 23.51/3.33  % (27924)------------------------------
% 23.51/3.33  % (27924)------------------------------
% 23.91/3.43  % (27889)Time limit reached!
% 23.91/3.43  % (27889)------------------------------
% 23.91/3.43  % (27889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.91/3.44  % (27889)Termination reason: Time limit
% 23.91/3.45  % (27889)Termination phase: Saturation
% 23.91/3.45  
% 23.91/3.45  % (27889)Memory used [KB]: 18293
% 23.91/3.45  % (27889)Time elapsed: 3.0000 s
% 23.91/3.45  % (27889)------------------------------
% 23.91/3.45  % (27889)------------------------------
% 24.50/3.45  % (27907)Time limit reached!
% 24.50/3.45  % (27907)------------------------------
% 24.50/3.45  % (27907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.50/3.45  % (27907)Termination reason: Time limit
% 24.50/3.45  
% 24.50/3.45  % (27907)Memory used [KB]: 23411
% 24.50/3.45  % (27907)Time elapsed: 2.834 s
% 24.50/3.45  % (27907)------------------------------
% 24.50/3.45  % (27907)------------------------------
% 25.11/3.52  % (27879)Refutation found. Thanks to Tanya!
% 25.11/3.52  % SZS status Theorem for theBenchmark
% 25.11/3.54  % SZS output start Proof for theBenchmark
% 25.11/3.54  fof(f69801,plain,(
% 25.11/3.54    $false),
% 25.11/3.54    inference(avatar_sat_refutation,[],[f57,f30859,f32801,f51859,f64309,f64598,f69754])).
% 25.11/3.54  fof(f69754,plain,(
% 25.11/3.54    spl4_1 | ~spl4_9),
% 25.11/3.54    inference(avatar_contradiction_clause,[],[f69753])).
% 25.11/3.54  fof(f69753,plain,(
% 25.11/3.54    $false | (spl4_1 | ~spl4_9)),
% 25.11/3.54    inference(subsumption_resolution,[],[f69693,f52])).
% 25.11/3.54  fof(f52,plain,(
% 25.11/3.54    ~r1_tarski(sK0,sK2) | spl4_1),
% 25.11/3.54    inference(avatar_component_clause,[],[f50])).
% 25.11/3.54  fof(f50,plain,(
% 25.11/3.54    spl4_1 <=> r1_tarski(sK0,sK2)),
% 25.11/3.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 25.11/3.54  fof(f69693,plain,(
% 25.11/3.54    r1_tarski(sK0,sK2) | ~spl4_9),
% 25.11/3.54    inference(superposition,[],[f67,f69567])).
% 25.11/3.54  fof(f69567,plain,(
% 25.11/3.54    sK0 = k3_xboole_0(sK0,sK2) | ~spl4_9),
% 25.11/3.54    inference(forward_demodulation,[],[f69566,f29])).
% 25.11/3.54  fof(f29,plain,(
% 25.11/3.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 25.11/3.54    inference(cnf_transformation,[],[f9])).
% 25.11/3.54  fof(f9,axiom,(
% 25.11/3.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 25.11/3.54  fof(f69566,plain,(
% 25.11/3.54    k3_xboole_0(sK0,sK2) = k5_xboole_0(sK0,k1_xboole_0) | ~spl4_9),
% 25.11/3.54    inference(forward_demodulation,[],[f69494,f152])).
% 25.11/3.54  fof(f152,plain,(
% 25.11/3.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 25.11/3.54    inference(forward_demodulation,[],[f138,f59])).
% 25.11/3.54  fof(f59,plain,(
% 25.11/3.54    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 25.11/3.54    inference(superposition,[],[f32,f29])).
% 25.11/3.54  fof(f32,plain,(
% 25.11/3.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 25.11/3.54    inference(cnf_transformation,[],[f2])).
% 25.11/3.54  fof(f2,axiom,(
% 25.11/3.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 25.11/3.54  fof(f138,plain,(
% 25.11/3.54    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 25.11/3.54    inference(superposition,[],[f39,f28])).
% 25.11/3.54  fof(f28,plain,(
% 25.11/3.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 25.11/3.54    inference(cnf_transformation,[],[f11])).
% 25.11/3.54  fof(f11,axiom,(
% 25.11/3.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 25.11/3.54  fof(f39,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 25.11/3.54    inference(cnf_transformation,[],[f10])).
% 25.11/3.54  fof(f10,axiom,(
% 25.11/3.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 25.11/3.54  fof(f69494,plain,(
% 25.11/3.54    k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK2))) | ~spl4_9),
% 25.11/3.54    inference(superposition,[],[f350,f69212])).
% 25.11/3.54  fof(f69212,plain,(
% 25.11/3.54    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK2),sK0) | ~spl4_9),
% 25.11/3.54    inference(superposition,[],[f65143,f95])).
% 25.11/3.54  fof(f95,plain,(
% 25.11/3.54    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 25.11/3.54    inference(superposition,[],[f74,f33])).
% 25.11/3.54  fof(f33,plain,(
% 25.11/3.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 25.11/3.54    inference(cnf_transformation,[],[f1])).
% 25.11/3.54  fof(f1,axiom,(
% 25.11/3.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 25.11/3.54  fof(f74,plain,(
% 25.11/3.54    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3)) )),
% 25.11/3.54    inference(resolution,[],[f35,f67])).
% 25.11/3.54  fof(f35,plain,(
% 25.11/3.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 25.11/3.54    inference(cnf_transformation,[],[f20])).
% 25.11/3.54  fof(f20,plain,(
% 25.11/3.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 25.11/3.54    inference(ennf_transformation,[],[f8])).
% 25.11/3.54  fof(f8,axiom,(
% 25.11/3.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 25.11/3.54  fof(f65143,plain,(
% 25.11/3.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK2),X0))) ) | ~spl4_9),
% 25.11/3.54    inference(forward_demodulation,[],[f65084,f360])).
% 25.11/3.54  fof(f360,plain,(
% 25.11/3.54    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4)) )),
% 25.11/3.54    inference(forward_demodulation,[],[f339,f28])).
% 25.11/3.54  fof(f339,plain,(
% 25.11/3.54    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X3,X3),X4)) )),
% 25.11/3.54    inference(superposition,[],[f41,f28])).
% 25.11/3.54  fof(f41,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 25.11/3.54    inference(cnf_transformation,[],[f5])).
% 25.11/3.54  fof(f5,axiom,(
% 25.11/3.54    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 25.11/3.54  fof(f65084,plain,(
% 25.11/3.54    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK2),X0))) ) | ~spl4_9),
% 25.11/3.54    inference(superposition,[],[f40,f64304])).
% 25.11/3.54  fof(f64304,plain,(
% 25.11/3.54    k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) | ~spl4_9),
% 25.11/3.54    inference(avatar_component_clause,[],[f64302])).
% 25.11/3.54  fof(f64302,plain,(
% 25.11/3.54    spl4_9 <=> k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2))),
% 25.11/3.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 25.11/3.54  fof(f40,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 25.11/3.54    inference(cnf_transformation,[],[f6])).
% 25.11/3.54  fof(f6,axiom,(
% 25.11/3.54    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 25.11/3.54  fof(f350,plain,(
% 25.11/3.54    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 25.11/3.54    inference(forward_demodulation,[],[f317,f33])).
% 25.11/3.54  fof(f317,plain,(
% 25.11/3.54    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 25.11/3.54    inference(superposition,[],[f41,f30])).
% 25.11/3.54  fof(f30,plain,(
% 25.11/3.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 25.11/3.54    inference(cnf_transformation,[],[f17])).
% 25.11/3.54  fof(f17,plain,(
% 25.11/3.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 25.11/3.54    inference(rectify,[],[f3])).
% 25.11/3.54  fof(f3,axiom,(
% 25.11/3.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 25.11/3.54  fof(f67,plain,(
% 25.11/3.54    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 25.11/3.54    inference(superposition,[],[f31,f33])).
% 25.11/3.54  fof(f31,plain,(
% 25.11/3.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 25.11/3.54    inference(cnf_transformation,[],[f7])).
% 25.11/3.54  fof(f7,axiom,(
% 25.11/3.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 25.11/3.54  fof(f64598,plain,(
% 25.11/3.54    ~spl4_10),
% 25.11/3.54    inference(avatar_contradiction_clause,[],[f64597])).
% 25.11/3.54  fof(f64597,plain,(
% 25.11/3.54    $false | ~spl4_10),
% 25.11/3.54    inference(subsumption_resolution,[],[f64448,f47])).
% 25.11/3.54  fof(f47,plain,(
% 25.11/3.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 25.11/3.54    inference(equality_resolution,[],[f38])).
% 25.11/3.54  fof(f38,plain,(
% 25.11/3.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 25.11/3.54    inference(cnf_transformation,[],[f24])).
% 25.11/3.54  fof(f24,plain,(
% 25.11/3.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 25.11/3.54    inference(flattening,[],[f23])).
% 25.11/3.54  fof(f23,plain,(
% 25.11/3.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 25.11/3.54    inference(nnf_transformation,[],[f12])).
% 25.11/3.54  fof(f12,axiom,(
% 25.11/3.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 25.11/3.54  fof(f64448,plain,(
% 25.11/3.54    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | ~spl4_10),
% 25.11/3.54    inference(backward_demodulation,[],[f26,f64308])).
% 25.11/3.54  fof(f64308,plain,(
% 25.11/3.54    k1_xboole_0 = sK1 | ~spl4_10),
% 25.11/3.54    inference(avatar_component_clause,[],[f64306])).
% 25.11/3.54  fof(f64306,plain,(
% 25.11/3.54    spl4_10 <=> k1_xboole_0 = sK1),
% 25.11/3.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 25.11/3.54  fof(f26,plain,(
% 25.11/3.54    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 25.11/3.54    inference(cnf_transformation,[],[f22])).
% 25.11/3.54  fof(f22,plain,(
% 25.11/3.54    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 25.11/3.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f21])).
% 25.11/3.54  fof(f21,plain,(
% 25.11/3.54    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 25.11/3.54    introduced(choice_axiom,[])).
% 25.11/3.54  fof(f19,plain,(
% 25.11/3.54    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 25.11/3.54    inference(flattening,[],[f18])).
% 25.11/3.54  fof(f18,plain,(
% 25.11/3.54    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 25.11/3.54    inference(ennf_transformation,[],[f16])).
% 25.11/3.54  fof(f16,negated_conjecture,(
% 25.11/3.54    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 25.11/3.54    inference(negated_conjecture,[],[f15])).
% 25.11/3.54  fof(f15,conjecture,(
% 25.11/3.54    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 25.11/3.54  fof(f64309,plain,(
% 25.11/3.54    spl4_9 | spl4_10 | ~spl4_2),
% 25.11/3.54    inference(avatar_split_clause,[],[f64300,f54,f64306,f64302])).
% 25.11/3.54  fof(f54,plain,(
% 25.11/3.54    spl4_2 <=> r1_tarski(sK1,sK3)),
% 25.11/3.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 25.11/3.54  fof(f64300,plain,(
% 25.11/3.54    k1_xboole_0 = sK1 | k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) | ~spl4_2),
% 25.11/3.54    inference(forward_demodulation,[],[f64299,f51933])).
% 25.11/3.54  fof(f51933,plain,(
% 25.11/3.54    sK1 = k3_xboole_0(sK1,sK3) | ~spl4_2),
% 25.11/3.54    inference(resolution,[],[f55,f35])).
% 25.11/3.54  fof(f55,plain,(
% 25.11/3.54    r1_tarski(sK1,sK3) | ~spl4_2),
% 25.11/3.54    inference(avatar_component_clause,[],[f54])).
% 25.11/3.54  fof(f64299,plain,(
% 25.11/3.54    k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | ~spl4_2),
% 25.11/3.54    inference(trivial_inequality_removal,[],[f64216])).
% 25.11/3.54  fof(f64216,plain,(
% 25.11/3.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | ~spl4_2),
% 25.11/3.54    inference(superposition,[],[f586,f52700])).
% 25.11/3.54  fof(f52700,plain,(
% 25.11/3.54    k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,sK2),sK3)) | ~spl4_2),
% 25.11/3.54    inference(forward_demodulation,[],[f52699,f28])).
% 25.11/3.54  fof(f52699,plain,(
% 25.11/3.54    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,sK2),sK3)) | ~spl4_2),
% 25.11/3.54    inference(forward_demodulation,[],[f52640,f51933])).
% 25.11/3.54  fof(f52640,plain,(
% 25.11/3.54    k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k5_xboole_0(sK0,sK2),sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))),
% 25.11/3.54    inference(superposition,[],[f27189,f72])).
% 25.11/3.54  fof(f72,plain,(
% 25.11/3.54    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 25.11/3.54    inference(resolution,[],[f35,f25])).
% 25.11/3.54  fof(f25,plain,(
% 25.11/3.54    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 25.11/3.54    inference(cnf_transformation,[],[f22])).
% 25.11/3.54  fof(f27189,plain,(
% 25.11/3.54    ( ! [X10,X8,X11,X9] : (k5_xboole_0(k2_zfmisc_1(X8,k3_xboole_0(X10,X11)),k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11))) = k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(k5_xboole_0(X8,X9),X11))) )),
% 25.11/3.54    inference(forward_demodulation,[],[f27072,f44])).
% 25.11/3.54  fof(f44,plain,(
% 25.11/3.54    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 25.11/3.54    inference(cnf_transformation,[],[f13])).
% 25.11/3.54  fof(f13,axiom,(
% 25.11/3.54    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 25.11/3.54  fof(f27072,plain,(
% 25.11/3.54    ( ! [X10,X8,X11,X9] : (k2_zfmisc_1(k3_xboole_0(X8,k5_xboole_0(X8,X9)),k3_xboole_0(X10,X11)) = k5_xboole_0(k2_zfmisc_1(X8,k3_xboole_0(X10,X11)),k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11)))) )),
% 25.11/3.54    inference(superposition,[],[f26626,f44])).
% 25.11/3.54  fof(f26626,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2)) = k2_zfmisc_1(k3_xboole_0(X0,k5_xboole_0(X0,X1)),X2)) )),
% 25.11/3.54    inference(backward_demodulation,[],[f17550,f26236])).
% 25.11/3.54  fof(f26236,plain,(
% 25.11/3.54    ( ! [X4,X2,X3] : (k2_zfmisc_1(k5_xboole_0(X2,k3_xboole_0(X2,X4)),X3) = k2_zfmisc_1(k3_xboole_0(X2,k5_xboole_0(X2,X4)),X3)) )),
% 25.11/3.54    inference(forward_demodulation,[],[f26235,f18135])).
% 25.11/3.54  fof(f18135,plain,(
% 25.11/3.54    ( ! [X4,X2,X3] : (k5_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(k3_xboole_0(X3,X2),X4)) = k2_zfmisc_1(k3_xboole_0(X2,k5_xboole_0(X2,X3)),X4)) )),
% 25.11/3.54    inference(forward_demodulation,[],[f18074,f350])).
% 25.11/3.54  fof(f18074,plain,(
% 25.11/3.54    ( ! [X4,X2,X3] : (k2_zfmisc_1(k5_xboole_0(X2,k3_xboole_0(X3,X2)),X4) = k5_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(k3_xboole_0(X3,X2),X4))) )),
% 25.11/3.54    inference(superposition,[],[f17550,f33])).
% 25.11/3.54  fof(f26235,plain,(
% 25.11/3.54    ( ! [X4,X2,X3] : (k2_zfmisc_1(k5_xboole_0(X2,k3_xboole_0(X2,X4)),X3) = k5_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(k3_xboole_0(X4,X2),X3))) )),
% 25.11/3.54    inference(forward_demodulation,[],[f1453,f571])).
% 25.11/3.54  fof(f571,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 25.11/3.54    inference(superposition,[],[f44,f30])).
% 25.11/3.54  fof(f1453,plain,(
% 25.11/3.54    ( ! [X4,X2,X3] : (k2_zfmisc_1(k5_xboole_0(X2,k3_xboole_0(X2,X4)),X3) = k5_xboole_0(k2_zfmisc_1(X2,X3),k3_xboole_0(k2_zfmisc_1(X4,X3),k2_zfmisc_1(X2,X3)))) )),
% 25.11/3.54    inference(superposition,[],[f46,f33])).
% 25.11/3.54  fof(f46,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 25.11/3.54    inference(definition_unfolding,[],[f42,f34,f34])).
% 25.11/3.54  fof(f34,plain,(
% 25.11/3.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 25.11/3.54    inference(cnf_transformation,[],[f4])).
% 25.11/3.54  fof(f4,axiom,(
% 25.11/3.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 25.11/3.54  fof(f42,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 25.11/3.54    inference(cnf_transformation,[],[f14])).
% 25.11/3.54  fof(f14,axiom,(
% 25.11/3.54    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 25.11/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 25.11/3.54  fof(f17550,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2))) )),
% 25.11/3.54    inference(backward_demodulation,[],[f46,f571])).
% 25.11/3.54  fof(f586,plain,(
% 25.11/3.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | k3_xboole_0(X0,X1) = k1_xboole_0 | k1_xboole_0 = k3_xboole_0(X2,X3)) )),
% 25.11/3.54    inference(superposition,[],[f36,f44])).
% 25.11/3.54  fof(f36,plain,(
% 25.11/3.54    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 25.11/3.54    inference(cnf_transformation,[],[f24])).
% 25.11/3.54  fof(f51859,plain,(
% 25.11/3.54    ~spl4_4),
% 25.11/3.54    inference(avatar_contradiction_clause,[],[f51858])).
% 25.11/3.54  fof(f51858,plain,(
% 25.11/3.54    $false | ~spl4_4),
% 25.11/3.54    inference(subsumption_resolution,[],[f51822,f48])).
% 25.11/3.54  fof(f48,plain,(
% 25.11/3.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 25.11/3.54    inference(equality_resolution,[],[f37])).
% 25.11/3.54  fof(f37,plain,(
% 25.11/3.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 25.11/3.54    inference(cnf_transformation,[],[f24])).
% 25.11/3.54  fof(f51822,plain,(
% 25.11/3.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | ~spl4_4),
% 25.11/3.54    inference(backward_demodulation,[],[f26,f30858])).
% 25.11/3.54  fof(f30858,plain,(
% 25.11/3.54    k1_xboole_0 = sK0 | ~spl4_4),
% 25.11/3.54    inference(avatar_component_clause,[],[f30856])).
% 25.11/3.54  fof(f30856,plain,(
% 25.11/3.54    spl4_4 <=> k1_xboole_0 = sK0),
% 25.11/3.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 25.11/3.54  fof(f32801,plain,(
% 25.11/3.54    spl4_2 | ~spl4_3),
% 25.11/3.54    inference(avatar_contradiction_clause,[],[f32800])).
% 25.11/3.54  fof(f32800,plain,(
% 25.11/3.54    $false | (spl4_2 | ~spl4_3)),
% 25.11/3.54    inference(subsumption_resolution,[],[f32702,f56])).
% 25.11/3.54  fof(f56,plain,(
% 25.11/3.54    ~r1_tarski(sK1,sK3) | spl4_2),
% 25.11/3.54    inference(avatar_component_clause,[],[f54])).
% 25.11/3.54  fof(f32702,plain,(
% 25.11/3.54    r1_tarski(sK1,sK3) | ~spl4_3),
% 25.11/3.54    inference(superposition,[],[f67,f32465])).
% 25.11/3.54  fof(f32465,plain,(
% 25.11/3.54    sK1 = k3_xboole_0(sK1,sK3) | ~spl4_3),
% 25.11/3.54    inference(forward_demodulation,[],[f32464,f152])).
% 25.11/3.54  fof(f32464,plain,(
% 25.11/3.54    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK3))) | ~spl4_3),
% 25.11/3.54    inference(forward_demodulation,[],[f32252,f29])).
% 25.11/3.54  fof(f32252,plain,(
% 25.11/3.54    k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK3))) = k5_xboole_0(sK1,k1_xboole_0) | ~spl4_3),
% 25.11/3.54    inference(superposition,[],[f350,f31425])).
% 25.11/3.54  fof(f31425,plain,(
% 25.11/3.54    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK3),sK1) | ~spl4_3),
% 25.11/3.54    inference(superposition,[],[f31185,f95])).
% 25.11/3.54  fof(f31185,plain,(
% 25.11/3.54    ( ! [X55] : (k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK3),X55))) ) | ~spl4_3),
% 25.11/3.54    inference(forward_demodulation,[],[f30980,f360])).
% 25.11/3.54  fof(f30980,plain,(
% 25.11/3.54    ( ! [X55] : (k3_xboole_0(k1_xboole_0,X55) = k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK3),X55))) ) | ~spl4_3),
% 25.11/3.54    inference(superposition,[],[f40,f30854])).
% 25.11/3.54  fof(f30854,plain,(
% 25.11/3.54    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK1,sK3)) | ~spl4_3),
% 25.11/3.54    inference(avatar_component_clause,[],[f30852])).
% 25.11/3.54  fof(f30852,plain,(
% 25.11/3.54    spl4_3 <=> k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK1,sK3))),
% 25.11/3.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 25.11/3.54  fof(f30859,plain,(
% 25.11/3.54    spl4_3 | spl4_4),
% 25.11/3.54    inference(avatar_split_clause,[],[f30742,f30856,f30852])).
% 25.11/3.54  fof(f30742,plain,(
% 25.11/3.54    k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK1,sK3))),
% 25.11/3.54    inference(trivial_inequality_removal,[],[f30715])).
% 25.11/3.54  fof(f30715,plain,(
% 25.11/3.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK1,sK3))),
% 25.11/3.54    inference(superposition,[],[f36,f30605])).
% 25.11/3.54  fof(f30605,plain,(
% 25.11/3.54    k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k5_xboole_0(sK1,sK3)))),
% 25.11/3.54    inference(forward_demodulation,[],[f30549,f28])).
% 25.11/3.54  fof(f30549,plain,(
% 25.11/3.54    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k5_xboole_0(sK1,sK3)))),
% 25.11/3.54    inference(superposition,[],[f24795,f30337])).
% 25.11/3.54  fof(f30337,plain,(
% 25.11/3.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 25.11/3.54    inference(forward_demodulation,[],[f30151,f83])).
% 25.11/3.54  fof(f83,plain,(
% 25.11/3.54    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 25.11/3.54    inference(superposition,[],[f73,f33])).
% 25.11/3.54  fof(f73,plain,(
% 25.11/3.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 25.11/3.54    inference(resolution,[],[f35,f31])).
% 25.11/3.54  fof(f30151,plain,(
% 25.11/3.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK3)))),
% 25.11/3.54    inference(superposition,[],[f27016,f556])).
% 25.11/3.54  fof(f556,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 25.11/3.54    inference(superposition,[],[f44,f30])).
% 25.11/3.54  fof(f27016,plain,(
% 25.11/3.54    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 25.11/3.54    inference(resolution,[],[f26988,f35])).
% 25.11/3.54  fof(f26988,plain,(
% 25.11/3.54    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 25.11/3.54    inference(superposition,[],[f22698,f120])).
% 25.11/3.54  fof(f120,plain,(
% 25.11/3.54    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),
% 25.11/3.54    inference(superposition,[],[f95,f72])).
% 25.11/3.54  fof(f22698,plain,(
% 25.11/3.54    ( ! [X19,X18] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X18,X19),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X19)))) )),
% 25.11/3.54    inference(forward_demodulation,[],[f22685,f44])).
% 25.11/3.54  fof(f22685,plain,(
% 25.11/3.54    ( ! [X19,X18] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X18,sK0),k3_xboole_0(X19,sK1)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X19)))) )),
% 25.11/3.54    inference(superposition,[],[f17026,f571])).
% 25.11/3.54  fof(f17026,plain,(
% 25.11/3.54    ( ! [X149,X150] : (r1_tarski(k3_xboole_0(X150,k2_zfmisc_1(sK0,k3_xboole_0(X149,sK1))),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X149)))) )),
% 25.11/3.54    inference(forward_demodulation,[],[f16829,f556])).
% 25.11/3.54  fof(f16829,plain,(
% 25.11/3.54    ( ! [X149,X150] : (r1_tarski(k3_xboole_0(X150,k3_xboole_0(k2_zfmisc_1(sK0,X149),k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,k3_xboole_0(sK1,X149)))) )),
% 25.11/3.54    inference(superposition,[],[f5546,f556])).
% 25.11/3.54  fof(f5546,plain,(
% 25.11/3.54    ( ! [X4,X3] : (r1_tarski(k3_xboole_0(X4,k3_xboole_0(X3,k2_zfmisc_1(sK0,sK1))),k3_xboole_0(k2_zfmisc_1(sK0,sK1),X3))) )),
% 25.11/3.54    inference(forward_demodulation,[],[f5545,f267])).
% 25.11/3.54  fof(f267,plain,(
% 25.11/3.54    ( ! [X0] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),X0) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X0,k2_zfmisc_1(sK2,sK3)))) )),
% 25.11/3.54    inference(superposition,[],[f232,f33])).
% 25.11/3.54  fof(f232,plain,(
% 25.11/3.54    ( ! [X14] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X14)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),X14)) )),
% 25.11/3.54    inference(superposition,[],[f40,f72])).
% 25.11/3.54  fof(f5545,plain,(
% 25.11/3.54    ( ! [X4,X3] : (r1_tarski(k3_xboole_0(X4,k3_xboole_0(X3,k2_zfmisc_1(sK0,sK1))),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X3,k2_zfmisc_1(sK2,sK3))))) )),
% 25.11/3.54    inference(forward_demodulation,[],[f5510,f33])).
% 25.11/3.54  fof(f5510,plain,(
% 25.11/3.54    ( ! [X4,X3] : (r1_tarski(k3_xboole_0(X4,k3_xboole_0(X3,k2_zfmisc_1(sK0,sK1))),k3_xboole_0(k3_xboole_0(X3,k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1)))) )),
% 25.11/3.54    inference(superposition,[],[f5451,f4884])).
% 25.11/3.54  fof(f4884,plain,(
% 25.11/3.54    ( ! [X10] : (k3_xboole_0(X10,k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X10,k2_zfmisc_1(sK2,sK3)))) )),
% 25.11/3.54    inference(superposition,[],[f228,f1078])).
% 25.11/3.54  fof(f1078,plain,(
% 25.11/3.54    ( ! [X26] : (k3_xboole_0(X26,k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k3_xboole_0(X26,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK3))) )),
% 25.11/3.54    inference(superposition,[],[f73,f519])).
% 25.11/3.54  fof(f519,plain,(
% 25.11/3.54    ( ! [X2] : (k3_xboole_0(X2,k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(X2,k2_zfmisc_1(sK0,sK1)))) )),
% 25.11/3.54    inference(superposition,[],[f233,f33])).
% 25.11/3.54  fof(f233,plain,(
% 25.11/3.54    ( ! [X15] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),X15) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK0,sK1),X15))) )),
% 25.11/3.54    inference(superposition,[],[f40,f120])).
% 25.11/3.54  fof(f228,plain,(
% 25.11/3.54    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(k3_xboole_0(X3,X2),X4)) )),
% 25.11/3.54    inference(superposition,[],[f40,f33])).
% 25.11/3.54  fof(f5451,plain,(
% 25.11/3.54    ( ! [X4,X3] : (r1_tarski(k3_xboole_0(X4,k3_xboole_0(k2_zfmisc_1(sK0,sK1),X3)),k3_xboole_0(X3,k2_zfmisc_1(sK0,sK1)))) )),
% 25.11/3.54    inference(forward_demodulation,[],[f5428,f40])).
% 25.11/3.54  fof(f5428,plain,(
% 25.11/3.54    ( ! [X4,X3] : (r1_tarski(k3_xboole_0(k3_xboole_0(X4,k2_zfmisc_1(sK0,sK1)),X3),k3_xboole_0(X3,k2_zfmisc_1(sK0,sK1)))) )),
% 25.11/3.54    inference(superposition,[],[f5270,f33])).
% 25.11/3.54  fof(f5270,plain,(
% 25.11/3.54    ( ! [X109,X108] : (r1_tarski(k3_xboole_0(X109,k3_xboole_0(X108,k2_zfmisc_1(sK0,sK1))),k3_xboole_0(X109,k2_zfmisc_1(sK0,sK1)))) )),
% 25.11/3.54    inference(superposition,[],[f247,f4884])).
% 25.11/3.54  fof(f247,plain,(
% 25.11/3.54    ( ! [X6,X8,X7] : (r1_tarski(k3_xboole_0(X6,k3_xboole_0(X7,X8)),k3_xboole_0(X6,X7))) )),
% 25.11/3.54    inference(superposition,[],[f31,f40])).
% 25.11/3.54  fof(f24795,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1))) = k2_zfmisc_1(X2,k3_xboole_0(X0,k5_xboole_0(X0,X1)))) )),
% 25.11/3.54    inference(backward_demodulation,[],[f16748,f24550])).
% 25.11/3.54  fof(f24550,plain,(
% 25.11/3.54    ( ! [X4,X2,X3] : (k2_zfmisc_1(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4))) = k2_zfmisc_1(X2,k3_xboole_0(X3,k5_xboole_0(X3,X4)))) )),
% 25.11/3.54    inference(forward_demodulation,[],[f24549,f17335])).
% 25.11/3.54  fof(f17335,plain,(
% 25.11/3.54    ( ! [X4,X2,X3] : (k5_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,k3_xboole_0(X3,X2))) = k2_zfmisc_1(X4,k3_xboole_0(X2,k5_xboole_0(X2,X3)))) )),
% 25.11/3.54    inference(forward_demodulation,[],[f17275,f350])).
% 25.11/3.54  fof(f17275,plain,(
% 25.11/3.54    ( ! [X4,X2,X3] : (k2_zfmisc_1(X4,k5_xboole_0(X2,k3_xboole_0(X3,X2))) = k5_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,k3_xboole_0(X3,X2)))) )),
% 25.11/3.54    inference(superposition,[],[f16748,f33])).
% 25.11/3.54  fof(f24549,plain,(
% 25.11/3.54    ( ! [X4,X2,X3] : (k2_zfmisc_1(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4))) = k5_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X2,k3_xboole_0(X4,X3)))) )),
% 25.11/3.54    inference(forward_demodulation,[],[f842,f556])).
% 25.11/3.54  fof(f842,plain,(
% 25.11/3.54    ( ! [X4,X2,X3] : (k2_zfmisc_1(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4))) = k5_xboole_0(k2_zfmisc_1(X2,X3),k3_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X2,X3)))) )),
% 25.11/3.54    inference(superposition,[],[f45,f33])).
% 25.11/3.54  fof(f45,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 25.11/3.54    inference(definition_unfolding,[],[f43,f34,f34])).
% 25.11/3.54  fof(f43,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 25.11/3.54    inference(cnf_transformation,[],[f14])).
% 25.11/3.54  fof(f16748,plain,(
% 25.11/3.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1)))) )),
% 25.11/3.54    inference(backward_demodulation,[],[f45,f556])).
% 25.11/3.54  fof(f57,plain,(
% 25.11/3.54    ~spl4_1 | ~spl4_2),
% 25.11/3.54    inference(avatar_split_clause,[],[f27,f54,f50])).
% 25.11/3.54  fof(f27,plain,(
% 25.11/3.54    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 25.11/3.54    inference(cnf_transformation,[],[f22])).
% 25.11/3.54  % SZS output end Proof for theBenchmark
% 25.11/3.54  % (27879)------------------------------
% 25.11/3.54  % (27879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.11/3.54  % (27879)Termination reason: Refutation
% 25.11/3.54  
% 25.11/3.54  % (27879)Memory used [KB]: 52067
% 25.11/3.54  % (27879)Time elapsed: 3.097 s
% 25.11/3.54  % (27879)------------------------------
% 25.11/3.54  % (27879)------------------------------
% 25.11/3.54  % (27875)Success in time 3.183 s
%------------------------------------------------------------------------------
