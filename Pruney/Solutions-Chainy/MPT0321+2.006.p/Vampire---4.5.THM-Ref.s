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
% DateTime   : Thu Dec  3 12:42:29 EST 2020

% Result     : Theorem 35.90s
% Output     : Refutation 35.90s
% Verified   : 
% Statistics : Number of formulae       :  155 (1871 expanded)
%              Number of leaves         :   18 ( 529 expanded)
%              Depth                    :   34
%              Number of atoms          :  309 (4732 expanded)
%              Number of equality atoms :  179 (3815 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33487,plain,(
    $false ),
    inference(subsumption_resolution,[],[f33486,f33464])).

fof(f33464,plain,(
    sK1 != sK3 ),
    inference(trivial_inequality_removal,[],[f29343])).

fof(f29343,plain,
    ( sK0 != sK0
    | sK1 != sK3 ),
    inference(backward_demodulation,[],[f35,f29341])).

fof(f29341,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f28972,f28330])).

fof(f28330,plain,(
    r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f28316,f109])).

fof(f109,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_tarski(X11,k3_xboole_0(X9,X10))
      | r1_tarski(X11,X9) ) ),
    inference(superposition,[],[f56,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f28316,plain,(
    r1_tarski(sK3,k3_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f28315,f103])).

fof(f103,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f75,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f64,f41])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f28315,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2)
    | r1_tarski(sK3,k3_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f28293,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f28293,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2)
    | r1_tarski(sK3,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f20779,f7399])).

fof(f7399,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f7398,f160])).

fof(f160,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = X2 ),
    inference(superposition,[],[f41,f150])).

fof(f150,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f147,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f147,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f43,f142])).

fof(f142,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f135,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f135,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f43,f37])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f7398,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f7397,f40])).

fof(f7397,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK2,sK0)),k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f7396,f39])).

fof(f7396,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f7395,f40])).

fof(f7395,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK3,sK1)) ),
    inference(forward_demodulation,[],[f7394,f41])).

fof(f7394,plain,(
    k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK3,sK1)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))) ),
    inference(forward_demodulation,[],[f7393,f1643])).

fof(f1643,plain,(
    ! [X10,X8,X11,X9] : k3_xboole_0(k2_zfmisc_1(X8,X11),k2_zfmisc_1(X9,X10)) = k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11)) ),
    inference(superposition,[],[f308,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f308,plain,(
    ! [X6,X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4)) = k2_zfmisc_1(k3_xboole_0(X5,X6),k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f59,f40])).

fof(f7393,plain,(
    k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK3,sK1)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,sK1))) ),
    inference(forward_demodulation,[],[f7392,f59])).

fof(f7392,plain,(
    k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK3,sK1)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,sK1))) ),
    inference(forward_demodulation,[],[f7284,f7183])).

fof(f7183,plain,(
    ! [X4] : k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X4)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK1,sK3),X4)) ),
    inference(forward_demodulation,[],[f7182,f40])).

fof(f7182,plain,(
    ! [X4] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK3,sK1),X4)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X4)) ),
    inference(forward_demodulation,[],[f7087,f40])).

fof(f7087,plain,(
    ! [X4] : k2_zfmisc_1(k3_xboole_0(sK2,sK0),k2_xboole_0(k3_xboole_0(sK3,sK1),X4)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK2,sK0),X4)) ),
    inference(superposition,[],[f2593,f150])).

fof(f2593,plain,(
    ! [X61,X59,X60] : k2_zfmisc_1(k3_xboole_0(sK2,X59),k2_xboole_0(k3_xboole_0(sK3,X60),X61)) = k2_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X59,X60)),k2_zfmisc_1(k3_xboole_0(sK2,X59),X61)) ),
    inference(superposition,[],[f316,f32])).

fof(f32,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f316,plain,(
    ! [X14,X17,X15,X18,X16] : k2_zfmisc_1(k3_xboole_0(X14,X15),k2_xboole_0(k3_xboole_0(X16,X17),X18)) = k2_xboole_0(k3_xboole_0(k2_zfmisc_1(X14,X16),k2_zfmisc_1(X15,X17)),k2_zfmisc_1(k3_xboole_0(X14,X15),X18)) ),
    inference(superposition,[],[f55,f59])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f7284,plain,(
    k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK3,sK1)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK1,sK3),k3_xboole_0(sK3,sK1))) ),
    inference(superposition,[],[f2607,f2291])).

fof(f2291,plain,(
    ! [X61,X59,X60] : k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,X59),X60),k3_xboole_0(sK3,X61)) = k2_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X59,X61)),k2_zfmisc_1(X60,k3_xboole_0(sK3,X61))) ),
    inference(superposition,[],[f314,f32])).

fof(f314,plain,(
    ! [X6,X4,X8,X7,X5] : k2_zfmisc_1(k2_xboole_0(k3_xboole_0(X4,X5),X8),k3_xboole_0(X6,X7)) = k2_xboole_0(k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7))) ),
    inference(superposition,[],[f54,f59])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f2607,plain,(
    ! [X61,X59,X60] : k2_zfmisc_1(k3_xboole_0(X59,sK2),k2_xboole_0(k3_xboole_0(X60,sK3),X61)) = k2_xboole_0(k3_xboole_0(k2_zfmisc_1(X59,X60),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(k3_xboole_0(X59,sK2),X61)) ),
    inference(superposition,[],[f316,f32])).

fof(f20779,plain,(
    ! [X156,X157] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X156,X157))
      | ~ r1_tarski(X156,sK2)
      | r1_tarski(sK3,X157) ) ),
    inference(subsumption_resolution,[],[f20723,f467])).

fof(f467,plain,(
    k1_xboole_0 != sK2 ),
    inference(resolution,[],[f98,f401])).

fof(f401,plain,(
    ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f400,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f400,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f393,f33])).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f393,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f384])).

fof(f384,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(superposition,[],[f48,f354])).

fof(f354,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f353,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(superposition,[],[f64,f72])).

fof(f72,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f41,f36])).

fof(f353,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f299,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f299,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(superposition,[],[f268,f63])).

fof(f63,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f268,plain,(
    ! [X0] :
      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))
      | ~ r1_tarski(sK2,X0) ) ),
    inference(superposition,[],[f222,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f222,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3)) ),
    inference(superposition,[],[f38,f193])).

fof(f193,plain,(
    ! [X0] : k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) ),
    inference(superposition,[],[f54,f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f98,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f51,f37])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f20723,plain,(
    ! [X156,X157] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X156,X157))
      | ~ r1_tarski(X156,sK2)
      | r1_tarski(sK3,X157)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f1143,f290])).

fof(f290,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0))
      | r1_tarski(sK3,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f58,f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f1143,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_zfmisc_1(X0,X3))
      | ~ r1_tarski(X2,k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f207,f82])).

fof(f82,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f44,f39])).

fof(f207,plain,(
    ! [X17,X15,X18,X16] :
      ( r1_tarski(X18,k2_zfmisc_1(k2_xboole_0(X15,X17),X16))
      | ~ r1_tarski(X18,k2_zfmisc_1(X17,X16)) ) ),
    inference(superposition,[],[f56,f54])).

fof(f28972,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK3,sK1) ),
    inference(backward_demodulation,[],[f25333,f28957])).

fof(f28957,plain,(
    sK2 = k3_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f28952,f103])).

fof(f28952,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2) ),
    inference(resolution,[],[f28730,f47])).

fof(f28730,plain,(
    r1_tarski(sK2,k3_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f28729,f637])).

fof(f637,plain,(
    k1_xboole_0 != sK3 ),
    inference(resolution,[],[f611,f98])).

fof(f611,plain,(
    ~ r1_tarski(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f610,f34])).

fof(f610,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f599,f33])).

fof(f599,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK3,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f590])).

fof(f590,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK3,k1_xboole_0) ),
    inference(superposition,[],[f48,f554])).

fof(f554,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f552,f94])).

fof(f552,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f522,f47])).

fof(f522,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | ~ r1_tarski(sK3,k1_xboole_0) ),
    inference(superposition,[],[f441,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f441,plain,(
    ! [X0] :
      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0))
      | ~ r1_tarski(sK3,X0) ) ),
    inference(superposition,[],[f362,f44])).

fof(f362,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(sK3,X0))) ),
    inference(superposition,[],[f38,f235])).

fof(f235,plain,(
    ! [X0] : k2_zfmisc_1(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) ),
    inference(superposition,[],[f55,f32])).

fof(f28729,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f28596,f60])).

fof(f28596,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK2,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f276,f28350])).

fof(f28350,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) ),
    inference(backward_demodulation,[],[f7399,f28337])).

fof(f28337,plain,(
    sK3 = k3_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f28332,f103])).

fof(f28332,plain,
    ( sK3 = k3_xboole_0(sK1,sK3)
    | ~ r1_tarski(k3_xboole_0(sK1,sK3),sK3) ),
    inference(resolution,[],[f28316,f47])).

fof(f276,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))
      | r1_tarski(sK2,X0)
      | k1_xboole_0 = sK3 ) ),
    inference(superposition,[],[f57,f32])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f25333,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK3,sK1) ),
    inference(forward_demodulation,[],[f25314,f37])).

fof(f25314,plain,
    ( k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ r1_tarski(sK3,sK1) ),
    inference(superposition,[],[f43,f25102])).

fof(f25102,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f25052,f125])).

fof(f125,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_xboole_0(X3,X4),X4)
      | k1_xboole_0 = k4_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f42,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f25052,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK2),sK2)
    | ~ r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f3894,f672])).

fof(f672,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X5,X4))
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f248,f44])).

fof(f248,plain,(
    ! [X4,X2,X3] : r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f38,f55])).

fof(f3894,plain,(
    ! [X16] :
      ( ~ r1_tarski(k2_zfmisc_1(X16,sK3),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(k2_xboole_0(X16,sK2),sK2) ) ),
    inference(subsumption_resolution,[],[f3893,f637])).

fof(f3893,plain,(
    ! [X16] :
      ( r1_tarski(k2_xboole_0(X16,sK2),sK2)
      | k1_xboole_0 = sK3
      | ~ r1_tarski(k2_zfmisc_1(X16,sK3),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3844,f60])).

fof(f3844,plain,(
    ! [X16] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(k2_xboole_0(X16,sK2),sK2)
      | k1_xboole_0 = sK3
      | ~ r1_tarski(k2_zfmisc_1(X16,sK3),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(superposition,[],[f279,f336])).

fof(f336,plain,(
    ! [X1] :
      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3)
      | ~ r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(superposition,[],[f196,f44])).

fof(f196,plain,(
    ! [X0] : k2_zfmisc_1(k2_xboole_0(X0,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f54,f32])).

fof(f279,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(X0,sK2)
      | k1_xboole_0 = sK3 ) ),
    inference(superposition,[],[f57,f32])).

fof(f35,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f33486,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f33485,f28330])).

fof(f33485,plain,
    ( ~ r1_tarski(sK3,sK1)
    | sK1 = sK3 ),
    inference(subsumption_resolution,[],[f29365,f60])).

fof(f29365,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK3,sK1)
    | sK1 = sK3 ),
    inference(backward_demodulation,[],[f332,f29341])).

fof(f332,plain,
    ( ~ r1_tarski(sK3,sK1)
    | sK1 = sK3
    | ~ r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f300,f47])).

fof(f300,plain,
    ( r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK2,sK0) ),
    inference(subsumption_resolution,[],[f296,f33])).

fof(f296,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f268,f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:35:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.50  % (20964)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (20993)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (20994)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (20969)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (20974)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (20985)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (20970)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (20986)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (20972)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (20976)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (20979)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (20987)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (20965)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (20980)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (20978)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (20994)Refutation not found, incomplete strategy% (20994)------------------------------
% 0.22/0.54  % (20994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20994)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20994)Memory used [KB]: 1663
% 0.22/0.54  % (20994)Time elapsed: 0.114 s
% 0.22/0.54  % (20994)------------------------------
% 0.22/0.54  % (20994)------------------------------
% 0.22/0.54  % (20966)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (20968)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (20981)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (20971)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (20989)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (20988)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (20991)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (20982)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (20983)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (20973)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (20984)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (20977)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (20975)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.57  % (20990)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.57  % (20992)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.55/0.58  % (20981)Refutation not found, incomplete strategy% (20981)------------------------------
% 1.55/0.58  % (20981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (20981)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (20981)Memory used [KB]: 10618
% 1.55/0.58  % (20981)Time elapsed: 0.172 s
% 1.55/0.58  % (20981)------------------------------
% 1.55/0.58  % (20981)------------------------------
% 2.03/0.64  % (21065)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.03/0.71  % (21066)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.25/0.85  % (20989)Time limit reached!
% 3.25/0.85  % (20989)------------------------------
% 3.25/0.85  % (20989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.25/0.85  % (20989)Termination reason: Time limit
% 3.25/0.85  
% 3.25/0.85  % (20989)Memory used [KB]: 13048
% 3.25/0.85  % (20989)Time elapsed: 0.433 s
% 3.25/0.85  % (20989)------------------------------
% 3.25/0.85  % (20989)------------------------------
% 3.25/0.85  % (20966)Time limit reached!
% 3.25/0.85  % (20966)------------------------------
% 3.25/0.85  % (20966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.25/0.85  % (20966)Termination reason: Time limit
% 3.25/0.85  
% 3.25/0.85  % (20966)Memory used [KB]: 6780
% 3.25/0.85  % (20966)Time elapsed: 0.441 s
% 3.25/0.85  % (20966)------------------------------
% 3.25/0.85  % (20966)------------------------------
% 3.74/0.94  % (20979)Time limit reached!
% 3.74/0.94  % (20979)------------------------------
% 3.74/0.94  % (20979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/0.96  % (20979)Termination reason: Time limit
% 3.74/0.96  % (20979)Termination phase: Saturation
% 3.74/0.96  
% 3.74/0.96  % (20979)Memory used [KB]: 4989
% 3.74/0.96  % (20979)Time elapsed: 0.500 s
% 3.74/0.96  % (20979)------------------------------
% 3.74/0.96  % (20979)------------------------------
% 4.46/0.98  % (20971)Time limit reached!
% 4.46/0.98  % (20971)------------------------------
% 4.46/0.98  % (20971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.98  % (20971)Termination reason: Time limit
% 4.46/0.98  
% 4.46/0.98  % (20971)Memory used [KB]: 14328
% 4.46/0.98  % (20971)Time elapsed: 0.520 s
% 4.46/0.98  % (20971)------------------------------
% 4.46/0.98  % (20971)------------------------------
% 4.46/0.99  % (21079)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.46/0.99  % (21078)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.74/1.03  % (20972)Time limit reached!
% 4.74/1.03  % (20972)------------------------------
% 4.74/1.03  % (20972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.03  % (20972)Termination reason: Time limit
% 4.74/1.03  
% 4.74/1.03  % (20972)Memory used [KB]: 6012
% 4.74/1.03  % (20972)Time elapsed: 0.620 s
% 4.74/1.03  % (20972)------------------------------
% 4.74/1.03  % (20972)------------------------------
% 5.00/1.10  % (21080)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.00/1.11  % (21081)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.64/1.17  % (21082)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.08/1.23  % (20965)Time limit reached!
% 6.08/1.23  % (20965)------------------------------
% 6.08/1.23  % (20965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.08/1.23  % (20965)Termination reason: Time limit
% 6.08/1.23  % (20965)Termination phase: Saturation
% 6.08/1.23  
% 6.08/1.23  % (20965)Memory used [KB]: 7036
% 6.08/1.23  % (20965)Time elapsed: 0.800 s
% 6.08/1.23  % (20965)------------------------------
% 6.08/1.23  % (20965)------------------------------
% 7.40/1.33  % (20968)Time limit reached!
% 7.40/1.33  % (20968)------------------------------
% 7.40/1.33  % (20968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.40/1.33  % (20968)Termination reason: Time limit
% 7.40/1.33  
% 7.40/1.33  % (20968)Memory used [KB]: 7675
% 7.40/1.33  % (20968)Time elapsed: 0.907 s
% 7.40/1.33  % (20968)------------------------------
% 7.40/1.33  % (20968)------------------------------
% 7.58/1.35  % (21083)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 8.24/1.43  % (20992)Time limit reached!
% 8.24/1.43  % (20992)------------------------------
% 8.24/1.43  % (20992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.24/1.43  % (20992)Termination reason: Time limit
% 8.24/1.43  % (20992)Termination phase: Saturation
% 8.24/1.43  
% 8.24/1.43  % (20992)Memory used [KB]: 12792
% 8.24/1.43  % (20992)Time elapsed: 1.0000 s
% 8.24/1.43  % (20992)------------------------------
% 8.24/1.43  % (20992)------------------------------
% 8.24/1.43  % (20977)Time limit reached!
% 8.24/1.43  % (20977)------------------------------
% 8.24/1.43  % (20977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.24/1.44  % (20977)Termination reason: Time limit
% 8.24/1.44  % (20977)Termination phase: Saturation
% 8.24/1.44  
% 8.24/1.44  % (20977)Memory used [KB]: 15351
% 8.24/1.44  % (20977)Time elapsed: 1.0000 s
% 8.24/1.44  % (20977)------------------------------
% 8.24/1.44  % (20977)------------------------------
% 8.24/1.47  % (21084)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 9.33/1.57  % (21085)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.33/1.57  % (21086)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.87/1.63  % (20964)Time limit reached!
% 9.87/1.63  % (20964)------------------------------
% 9.87/1.63  % (20964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.87/1.65  % (20964)Termination reason: Time limit
% 9.87/1.65  
% 9.87/1.65  % (20964)Memory used [KB]: 9466
% 9.87/1.65  % (20964)Time elapsed: 1.231 s
% 9.87/1.65  % (20964)------------------------------
% 9.87/1.65  % (20964)------------------------------
% 9.87/1.68  % (21082)Time limit reached!
% 9.87/1.68  % (21082)------------------------------
% 9.87/1.68  % (21082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.87/1.68  % (21082)Termination reason: Time limit
% 9.87/1.68  
% 9.87/1.68  % (21082)Memory used [KB]: 18293
% 9.87/1.68  % (21082)Time elapsed: 0.624 s
% 9.87/1.68  % (21082)------------------------------
% 9.87/1.68  % (21082)------------------------------
% 10.45/1.72  % (21078)Time limit reached!
% 10.45/1.72  % (21078)------------------------------
% 10.45/1.72  % (21078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.45/1.72  % (21078)Termination reason: Time limit
% 10.45/1.72  
% 10.45/1.72  % (21078)Memory used [KB]: 15095
% 10.45/1.72  % (21078)Time elapsed: 0.826 s
% 10.45/1.72  % (21078)------------------------------
% 10.45/1.72  % (21078)------------------------------
% 10.45/1.73  % (20970)Time limit reached!
% 10.45/1.73  % (20970)------------------------------
% 10.45/1.73  % (20970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.45/1.73  % (20970)Termination reason: Time limit
% 10.45/1.73  % (20970)Termination phase: Saturation
% 10.45/1.73  
% 10.45/1.73  % (20970)Memory used [KB]: 19061
% 10.45/1.73  % (20970)Time elapsed: 1.300 s
% 10.45/1.73  % (20970)------------------------------
% 10.45/1.73  % (20970)------------------------------
% 11.23/1.80  % (21087)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 11.23/1.80  % (21088)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 11.23/1.86  % (21089)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.23/1.86  % (21090)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 12.89/2.01  % (20991)Time limit reached!
% 12.89/2.01  % (20991)------------------------------
% 12.89/2.01  % (20991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.89/2.01  % (20991)Termination reason: Time limit
% 12.89/2.01  % (20991)Termination phase: Saturation
% 12.89/2.01  
% 12.89/2.01  % (20991)Memory used [KB]: 20340
% 12.89/2.01  % (20991)Time elapsed: 1.600 s
% 12.89/2.01  % (20991)------------------------------
% 12.89/2.01  % (20991)------------------------------
% 13.49/2.14  % (21089)Time limit reached!
% 13.49/2.14  % (21089)------------------------------
% 13.49/2.14  % (21089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.49/2.14  % (21089)Termination reason: Time limit
% 13.49/2.14  % (21089)Termination phase: Saturation
% 13.49/2.14  
% 13.49/2.14  % (21089)Memory used [KB]: 13816
% 13.49/2.14  % (21089)Time elapsed: 0.400 s
% 13.49/2.14  % (21089)------------------------------
% 13.49/2.14  % (21089)------------------------------
% 13.49/2.15  % (21091)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 14.58/2.24  % (20985)Time limit reached!
% 14.58/2.24  % (20985)------------------------------
% 14.58/2.24  % (20985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.58/2.24  % (20985)Termination reason: Time limit
% 14.58/2.24  % (20985)Termination phase: Saturation
% 14.58/2.24  
% 14.58/2.24  % (20985)Memory used [KB]: 31470
% 14.58/2.24  % (20985)Time elapsed: 1.800 s
% 14.58/2.24  % (20985)------------------------------
% 14.58/2.24  % (20985)------------------------------
% 14.58/2.26  % (21085)Time limit reached!
% 14.58/2.26  % (21085)------------------------------
% 14.58/2.26  % (21085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.58/2.27  % (21085)Termination reason: Time limit
% 14.58/2.27  % (21085)Termination phase: Saturation
% 14.58/2.27  
% 14.58/2.27  % (21085)Memory used [KB]: 18038
% 14.58/2.27  % (21085)Time elapsed: 0.800 s
% 14.58/2.27  % (21092)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 14.58/2.27  % (21085)------------------------------
% 14.58/2.27  % (21085)------------------------------
% 15.40/2.37  % (21093)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 16.01/2.40  % (21094)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 16.01/2.45  % (21091)Time limit reached!
% 16.01/2.45  % (21091)------------------------------
% 16.01/2.45  % (21091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.01/2.47  % (21091)Termination reason: Time limit
% 16.01/2.47  % (21091)Termination phase: Saturation
% 16.01/2.47  
% 16.01/2.47  % (21091)Memory used [KB]: 7803
% 16.01/2.47  % (21091)Time elapsed: 0.400 s
% 16.01/2.47  % (21091)------------------------------
% 16.01/2.47  % (21091)------------------------------
% 16.95/2.60  % (21095)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 17.67/2.66  % (21093)Time limit reached!
% 17.67/2.66  % (21093)------------------------------
% 17.67/2.66  % (21093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.67/2.66  % (21093)Termination reason: Time limit
% 17.67/2.66  
% 17.67/2.66  % (21093)Memory used [KB]: 9083
% 17.67/2.66  % (21093)Time elapsed: 0.405 s
% 17.67/2.66  % (21093)------------------------------
% 17.67/2.66  % (21093)------------------------------
% 17.67/2.68  % (21092)Time limit reached!
% 17.67/2.68  % (21092)------------------------------
% 17.67/2.68  % (21092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.67/2.69  % (21092)Termination reason: Time limit
% 17.67/2.69  
% 17.67/2.69  % (21092)Memory used [KB]: 13048
% 17.67/2.69  % (21092)Time elapsed: 0.526 s
% 17.67/2.69  % (21092)------------------------------
% 17.67/2.69  % (21092)------------------------------
% 19.09/2.79  % (21096)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 19.42/2.89  % (20980)Time limit reached!
% 19.42/2.89  % (20980)------------------------------
% 19.42/2.89  % (20980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.42/2.89  % (21095)Time limit reached!
% 19.42/2.89  % (21095)------------------------------
% 19.42/2.89  % (21095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.42/2.89  % (21095)Termination reason: Time limit
% 19.42/2.89  % (21095)Termination phase: Saturation
% 19.42/2.89  
% 19.42/2.89  % (21095)Memory used [KB]: 3837
% 19.42/2.89  % (21095)Time elapsed: 0.409 s
% 19.42/2.89  % (21095)------------------------------
% 19.42/2.89  % (21095)------------------------------
% 19.42/2.90  % (20980)Termination reason: Time limit
% 19.42/2.90  % (20980)Termination phase: Saturation
% 19.42/2.90  
% 19.42/2.90  % (20980)Memory used [KB]: 19957
% 19.42/2.90  % (20980)Time elapsed: 2.400 s
% 19.42/2.90  % (20980)------------------------------
% 19.42/2.90  % (20980)------------------------------
% 21.54/3.10  % (21096)Time limit reached!
% 21.54/3.10  % (21096)------------------------------
% 21.54/3.10  % (21096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.54/3.10  % (21096)Termination reason: Time limit
% 21.54/3.10  
% 21.54/3.10  % (21096)Memory used [KB]: 7547
% 21.54/3.10  % (21096)Time elapsed: 0.417 s
% 21.54/3.10  % (21096)------------------------------
% 21.54/3.10  % (21096)------------------------------
% 25.09/3.56  % (20973)Time limit reached!
% 25.09/3.56  % (20973)------------------------------
% 25.09/3.56  % (20973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.09/3.57  % (20973)Termination reason: Time limit
% 25.09/3.57  % (20973)Termination phase: Saturation
% 25.09/3.57  
% 25.09/3.57  % (20973)Memory used [KB]: 15863
% 25.09/3.57  % (20973)Time elapsed: 3.100 s
% 25.09/3.57  % (20973)------------------------------
% 25.09/3.57  % (20973)------------------------------
% 25.70/3.62  % (20976)Time limit reached!
% 25.70/3.62  % (20976)------------------------------
% 25.70/3.62  % (20976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.70/3.62  % (20976)Termination reason: Time limit
% 25.70/3.62  
% 25.70/3.62  % (20976)Memory used [KB]: 42984
% 25.70/3.62  % (20976)Time elapsed: 3.160 s
% 25.70/3.62  % (20976)------------------------------
% 25.70/3.62  % (20976)------------------------------
% 26.23/3.76  % (20984)Time limit reached!
% 26.23/3.76  % (20984)------------------------------
% 26.23/3.76  % (20984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.23/3.76  % (20984)Termination reason: Time limit
% 26.23/3.76  
% 26.23/3.76  % (20984)Memory used [KB]: 37483
% 26.23/3.76  % (20984)Time elapsed: 3.326 s
% 26.23/3.76  % (20984)------------------------------
% 26.23/3.76  % (20984)------------------------------
% 30.66/4.28  % (21079)Time limit reached!
% 30.66/4.28  % (21079)------------------------------
% 30.66/4.28  % (21079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.15/4.30  % (21079)Termination reason: Time limit
% 31.15/4.30  % (21079)Termination phase: Saturation
% 31.15/4.30  
% 31.15/4.30  % (21079)Memory used [KB]: 38890
% 31.15/4.30  % (21079)Time elapsed: 3.405 s
% 31.15/4.30  % (21079)------------------------------
% 31.15/4.30  % (21079)------------------------------
% 31.75/4.36  % (21084)Time limit reached!
% 31.75/4.36  % (21084)------------------------------
% 31.75/4.36  % (21084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.75/4.36  % (21084)Termination reason: Time limit
% 31.75/4.36  % (21084)Termination phase: Saturation
% 31.75/4.36  
% 31.75/4.36  % (21084)Memory used [KB]: 29679
% 31.75/4.36  % (21084)Time elapsed: 3.0000 s
% 31.75/4.36  % (21084)------------------------------
% 31.75/4.36  % (21084)------------------------------
% 33.11/4.57  % (21083)Time limit reached!
% 33.11/4.57  % (21083)------------------------------
% 33.11/4.57  % (21083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.11/4.57  % (21083)Termination reason: Time limit
% 33.11/4.57  % (21083)Termination phase: Saturation
% 33.11/4.57  
% 33.11/4.57  % (21083)Memory used [KB]: 36971
% 33.11/4.57  % (21083)Time elapsed: 3.300 s
% 33.11/4.57  % (21083)------------------------------
% 33.11/4.57  % (21083)------------------------------
% 35.90/4.93  % (20974)Refutation found. Thanks to Tanya!
% 35.90/4.93  % SZS status Theorem for theBenchmark
% 35.90/4.93  % SZS output start Proof for theBenchmark
% 35.90/4.93  fof(f33487,plain,(
% 35.90/4.93    $false),
% 35.90/4.93    inference(subsumption_resolution,[],[f33486,f33464])).
% 35.90/4.93  fof(f33464,plain,(
% 35.90/4.93    sK1 != sK3),
% 35.90/4.93    inference(trivial_inequality_removal,[],[f29343])).
% 35.90/4.93  fof(f29343,plain,(
% 35.90/4.93    sK0 != sK0 | sK1 != sK3),
% 35.90/4.93    inference(backward_demodulation,[],[f35,f29341])).
% 35.90/4.93  fof(f29341,plain,(
% 35.90/4.93    sK0 = sK2),
% 35.90/4.93    inference(subsumption_resolution,[],[f28972,f28330])).
% 35.90/4.93  fof(f28330,plain,(
% 35.90/4.93    r1_tarski(sK3,sK1)),
% 35.90/4.93    inference(resolution,[],[f28316,f109])).
% 35.90/4.93  fof(f109,plain,(
% 35.90/4.93    ( ! [X10,X11,X9] : (~r1_tarski(X11,k3_xboole_0(X9,X10)) | r1_tarski(X11,X9)) )),
% 35.90/4.93    inference(superposition,[],[f56,f41])).
% 35.90/4.93  fof(f41,plain,(
% 35.90/4.93    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 35.90/4.93    inference(cnf_transformation,[],[f8])).
% 35.90/4.93  fof(f8,axiom,(
% 35.90/4.93    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 35.90/4.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 35.90/4.93  fof(f56,plain,(
% 35.90/4.93    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 35.90/4.93    inference(cnf_transformation,[],[f23])).
% 35.90/4.93  fof(f23,plain,(
% 35.90/4.93    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 35.90/4.93    inference(ennf_transformation,[],[f5])).
% 35.90/4.93  fof(f5,axiom,(
% 35.90/4.93    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 35.90/4.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 35.90/4.93  fof(f28316,plain,(
% 35.90/4.93    r1_tarski(sK3,k3_xboole_0(sK1,sK3))),
% 35.90/4.93    inference(subsumption_resolution,[],[f28315,f103])).
% 35.90/4.93  fof(f103,plain,(
% 35.90/4.93    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 35.90/4.93    inference(superposition,[],[f75,f40])).
% 35.90/4.93  fof(f40,plain,(
% 35.90/4.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.90/4.93    inference(cnf_transformation,[],[f2])).
% 35.90/4.94  fof(f2,axiom,(
% 35.90/4.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 35.90/4.94  fof(f75,plain,(
% 35.90/4.94    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 35.90/4.94    inference(superposition,[],[f64,f41])).
% 35.90/4.94  fof(f64,plain,(
% 35.90/4.94    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 35.90/4.94    inference(superposition,[],[f38,f39])).
% 35.90/4.94  fof(f39,plain,(
% 35.90/4.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 35.90/4.94    inference(cnf_transformation,[],[f1])).
% 35.90/4.94  fof(f1,axiom,(
% 35.90/4.94    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 35.90/4.94  fof(f38,plain,(
% 35.90/4.94    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 35.90/4.94    inference(cnf_transformation,[],[f13])).
% 35.90/4.94  fof(f13,axiom,(
% 35.90/4.94    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 35.90/4.94  fof(f28315,plain,(
% 35.90/4.94    ~r1_tarski(k3_xboole_0(sK0,sK2),sK2) | r1_tarski(sK3,k3_xboole_0(sK1,sK3))),
% 35.90/4.94    inference(subsumption_resolution,[],[f28293,f60])).
% 35.90/4.94  fof(f60,plain,(
% 35.90/4.94    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.90/4.94    inference(equality_resolution,[],[f46])).
% 35.90/4.94  fof(f46,plain,(
% 35.90/4.94    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 35.90/4.94    inference(cnf_transformation,[],[f28])).
% 35.90/4.94  fof(f28,plain,(
% 35.90/4.94    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.90/4.94    inference(flattening,[],[f27])).
% 35.90/4.94  fof(f27,plain,(
% 35.90/4.94    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.90/4.94    inference(nnf_transformation,[],[f3])).
% 35.90/4.94  fof(f3,axiom,(
% 35.90/4.94    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 35.90/4.94  fof(f28293,plain,(
% 35.90/4.94    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(k3_xboole_0(sK0,sK2),sK2) | r1_tarski(sK3,k3_xboole_0(sK1,sK3))),
% 35.90/4.94    inference(superposition,[],[f20779,f7399])).
% 35.90/4.94  fof(f7399,plain,(
% 35.90/4.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 35.90/4.94    inference(forward_demodulation,[],[f7398,f160])).
% 35.90/4.94  fof(f160,plain,(
% 35.90/4.94    ( ! [X2] : (k2_xboole_0(X2,X2) = X2) )),
% 35.90/4.94    inference(superposition,[],[f41,f150])).
% 35.90/4.94  fof(f150,plain,(
% 35.90/4.94    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 35.90/4.94    inference(forward_demodulation,[],[f147,f37])).
% 35.90/4.94  fof(f37,plain,(
% 35.90/4.94    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.90/4.94    inference(cnf_transformation,[],[f10])).
% 35.90/4.94  fof(f10,axiom,(
% 35.90/4.94    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 35.90/4.94  fof(f147,plain,(
% 35.90/4.94    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 35.90/4.94    inference(superposition,[],[f43,f142])).
% 35.90/4.94  fof(f142,plain,(
% 35.90/4.94    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 35.90/4.94    inference(forward_demodulation,[],[f135,f36])).
% 35.90/4.94  fof(f36,plain,(
% 35.90/4.94    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 35.90/4.94    inference(cnf_transformation,[],[f9])).
% 35.90/4.94  fof(f9,axiom,(
% 35.90/4.94    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 35.90/4.94  fof(f135,plain,(
% 35.90/4.94    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 35.90/4.94    inference(superposition,[],[f43,f37])).
% 35.90/4.94  fof(f43,plain,(
% 35.90/4.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.90/4.94    inference(cnf_transformation,[],[f12])).
% 35.90/4.94  fof(f12,axiom,(
% 35.90/4.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 35.90/4.94  fof(f7398,plain,(
% 35.90/4.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3))),
% 35.90/4.94    inference(forward_demodulation,[],[f7397,f40])).
% 35.90/4.94  fof(f7397,plain,(
% 35.90/4.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK2,sK0)),k3_xboole_0(sK1,sK3))),
% 35.90/4.94    inference(forward_demodulation,[],[f7396,f39])).
% 35.90/4.94  fof(f7396,plain,(
% 35.90/4.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3))),
% 35.90/4.94    inference(forward_demodulation,[],[f7395,f40])).
% 35.90/4.94  fof(f7395,plain,(
% 35.90/4.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK3,sK1))),
% 35.90/4.94    inference(forward_demodulation,[],[f7394,f41])).
% 35.90/4.94  fof(f7394,plain,(
% 35.90/4.94    k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK3,sK1)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 35.90/4.94    inference(forward_demodulation,[],[f7393,f1643])).
% 35.90/4.94  fof(f1643,plain,(
% 35.90/4.94    ( ! [X10,X8,X11,X9] : (k3_xboole_0(k2_zfmisc_1(X8,X11),k2_zfmisc_1(X9,X10)) = k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11))) )),
% 35.90/4.94    inference(superposition,[],[f308,f59])).
% 35.90/4.94  fof(f59,plain,(
% 35.90/4.94    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 35.90/4.94    inference(cnf_transformation,[],[f17])).
% 35.90/4.94  fof(f17,axiom,(
% 35.90/4.94    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 35.90/4.94  fof(f308,plain,(
% 35.90/4.94    ( ! [X6,X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4)) = k2_zfmisc_1(k3_xboole_0(X5,X6),k3_xboole_0(X4,X3))) )),
% 35.90/4.94    inference(superposition,[],[f59,f40])).
% 35.90/4.94  fof(f7393,plain,(
% 35.90/4.94    k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK3,sK1)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,sK1)))),
% 35.90/4.94    inference(forward_demodulation,[],[f7392,f59])).
% 35.90/4.94  fof(f7392,plain,(
% 35.90/4.94    k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK3,sK1)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,sK1)))),
% 35.90/4.94    inference(forward_demodulation,[],[f7284,f7183])).
% 35.90/4.94  fof(f7183,plain,(
% 35.90/4.94    ( ! [X4] : (k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X4)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK1,sK3),X4))) )),
% 35.90/4.94    inference(forward_demodulation,[],[f7182,f40])).
% 35.90/4.94  fof(f7182,plain,(
% 35.90/4.94    ( ! [X4] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK3,sK1),X4)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X4))) )),
% 35.90/4.94    inference(forward_demodulation,[],[f7087,f40])).
% 35.90/4.94  fof(f7087,plain,(
% 35.90/4.94    ( ! [X4] : (k2_zfmisc_1(k3_xboole_0(sK2,sK0),k2_xboole_0(k3_xboole_0(sK3,sK1),X4)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK2,sK0),X4))) )),
% 35.90/4.94    inference(superposition,[],[f2593,f150])).
% 35.90/4.94  fof(f2593,plain,(
% 35.90/4.94    ( ! [X61,X59,X60] : (k2_zfmisc_1(k3_xboole_0(sK2,X59),k2_xboole_0(k3_xboole_0(sK3,X60),X61)) = k2_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X59,X60)),k2_zfmisc_1(k3_xboole_0(sK2,X59),X61))) )),
% 35.90/4.94    inference(superposition,[],[f316,f32])).
% 35.90/4.94  fof(f32,plain,(
% 35.90/4.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 35.90/4.94    inference(cnf_transformation,[],[f26])).
% 35.90/4.94  fof(f26,plain,(
% 35.90/4.94    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 35.90/4.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f25])).
% 35.90/4.94  fof(f25,plain,(
% 35.90/4.94    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 35.90/4.94    introduced(choice_axiom,[])).
% 35.90/4.94  fof(f21,plain,(
% 35.90/4.94    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 35.90/4.94    inference(flattening,[],[f20])).
% 35.90/4.94  fof(f20,plain,(
% 35.90/4.94    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 35.90/4.94    inference(ennf_transformation,[],[f19])).
% 35.90/4.94  fof(f19,negated_conjecture,(
% 35.90/4.94    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 35.90/4.94    inference(negated_conjecture,[],[f18])).
% 35.90/4.94  fof(f18,conjecture,(
% 35.90/4.94    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 35.90/4.94  fof(f316,plain,(
% 35.90/4.94    ( ! [X14,X17,X15,X18,X16] : (k2_zfmisc_1(k3_xboole_0(X14,X15),k2_xboole_0(k3_xboole_0(X16,X17),X18)) = k2_xboole_0(k3_xboole_0(k2_zfmisc_1(X14,X16),k2_zfmisc_1(X15,X17)),k2_zfmisc_1(k3_xboole_0(X14,X15),X18))) )),
% 35.90/4.94    inference(superposition,[],[f55,f59])).
% 35.90/4.94  fof(f55,plain,(
% 35.90/4.94    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 35.90/4.94    inference(cnf_transformation,[],[f16])).
% 35.90/4.94  fof(f16,axiom,(
% 35.90/4.94    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 35.90/4.94  fof(f7284,plain,(
% 35.90/4.94    k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK3,sK1)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK1,sK3),k3_xboole_0(sK3,sK1)))),
% 35.90/4.94    inference(superposition,[],[f2607,f2291])).
% 35.90/4.94  fof(f2291,plain,(
% 35.90/4.94    ( ! [X61,X59,X60] : (k2_zfmisc_1(k2_xboole_0(k3_xboole_0(sK2,X59),X60),k3_xboole_0(sK3,X61)) = k2_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X59,X61)),k2_zfmisc_1(X60,k3_xboole_0(sK3,X61)))) )),
% 35.90/4.94    inference(superposition,[],[f314,f32])).
% 35.90/4.94  fof(f314,plain,(
% 35.90/4.94    ( ! [X6,X4,X8,X7,X5] : (k2_zfmisc_1(k2_xboole_0(k3_xboole_0(X4,X5),X8),k3_xboole_0(X6,X7)) = k2_xboole_0(k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)),k2_zfmisc_1(X8,k3_xboole_0(X6,X7)))) )),
% 35.90/4.94    inference(superposition,[],[f54,f59])).
% 35.90/4.94  fof(f54,plain,(
% 35.90/4.94    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 35.90/4.94    inference(cnf_transformation,[],[f16])).
% 35.90/4.94  fof(f2607,plain,(
% 35.90/4.94    ( ! [X61,X59,X60] : (k2_zfmisc_1(k3_xboole_0(X59,sK2),k2_xboole_0(k3_xboole_0(X60,sK3),X61)) = k2_xboole_0(k3_xboole_0(k2_zfmisc_1(X59,X60),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(k3_xboole_0(X59,sK2),X61))) )),
% 35.90/4.94    inference(superposition,[],[f316,f32])).
% 35.90/4.94  fof(f20779,plain,(
% 35.90/4.94    ( ! [X156,X157] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X156,X157)) | ~r1_tarski(X156,sK2) | r1_tarski(sK3,X157)) )),
% 35.90/4.94    inference(subsumption_resolution,[],[f20723,f467])).
% 35.90/4.94  fof(f467,plain,(
% 35.90/4.94    k1_xboole_0 != sK2),
% 35.90/4.94    inference(resolution,[],[f98,f401])).
% 35.90/4.94  fof(f401,plain,(
% 35.90/4.94    ~r1_tarski(sK2,k1_xboole_0)),
% 35.90/4.94    inference(subsumption_resolution,[],[f400,f34])).
% 35.90/4.94  fof(f34,plain,(
% 35.90/4.94    k1_xboole_0 != sK1),
% 35.90/4.94    inference(cnf_transformation,[],[f26])).
% 35.90/4.94  fof(f400,plain,(
% 35.90/4.94    k1_xboole_0 = sK1 | ~r1_tarski(sK2,k1_xboole_0)),
% 35.90/4.94    inference(subsumption_resolution,[],[f393,f33])).
% 35.90/4.94  fof(f33,plain,(
% 35.90/4.94    k1_xboole_0 != sK0),
% 35.90/4.94    inference(cnf_transformation,[],[f26])).
% 35.90/4.94  fof(f393,plain,(
% 35.90/4.94    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~r1_tarski(sK2,k1_xboole_0)),
% 35.90/4.94    inference(trivial_inequality_removal,[],[f384])).
% 35.90/4.94  fof(f384,plain,(
% 35.90/4.94    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~r1_tarski(sK2,k1_xboole_0)),
% 35.90/4.94    inference(superposition,[],[f48,f354])).
% 35.90/4.94  fof(f354,plain,(
% 35.90/4.94    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(sK2,k1_xboole_0)),
% 35.90/4.94    inference(subsumption_resolution,[],[f353,f94])).
% 35.90/4.94  fof(f94,plain,(
% 35.90/4.94    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 35.90/4.94    inference(superposition,[],[f64,f72])).
% 35.90/4.94  fof(f72,plain,(
% 35.90/4.94    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.90/4.94    inference(superposition,[],[f41,f36])).
% 35.90/4.94  fof(f353,plain,(
% 35.90/4.94    ~r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 35.90/4.94    inference(resolution,[],[f299,f47])).
% 35.90/4.94  fof(f47,plain,(
% 35.90/4.94    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 35.90/4.94    inference(cnf_transformation,[],[f28])).
% 35.90/4.94  fof(f299,plain,(
% 35.90/4.94    r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) | ~r1_tarski(sK2,k1_xboole_0)),
% 35.90/4.94    inference(superposition,[],[f268,f63])).
% 35.90/4.94  fof(f63,plain,(
% 35.90/4.94    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 35.90/4.94    inference(equality_resolution,[],[f49])).
% 35.90/4.94  fof(f49,plain,(
% 35.90/4.94    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 35.90/4.94    inference(cnf_transformation,[],[f30])).
% 35.90/4.94  fof(f30,plain,(
% 35.90/4.94    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 35.90/4.94    inference(flattening,[],[f29])).
% 35.90/4.94  fof(f29,plain,(
% 35.90/4.94    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 35.90/4.94    inference(nnf_transformation,[],[f14])).
% 35.90/4.94  fof(f14,axiom,(
% 35.90/4.94    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 35.90/4.94  fof(f268,plain,(
% 35.90/4.94    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) | ~r1_tarski(sK2,X0)) )),
% 35.90/4.94    inference(superposition,[],[f222,f44])).
% 35.90/4.94  fof(f44,plain,(
% 35.90/4.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 35.90/4.94    inference(cnf_transformation,[],[f22])).
% 35.90/4.94  fof(f22,plain,(
% 35.90/4.94    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 35.90/4.94    inference(ennf_transformation,[],[f6])).
% 35.90/4.94  fof(f6,axiom,(
% 35.90/4.94    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 35.90/4.94  fof(f222,plain,(
% 35.90/4.94    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3))) )),
% 35.90/4.94    inference(superposition,[],[f38,f193])).
% 35.90/4.94  fof(f193,plain,(
% 35.90/4.94    ( ! [X0] : (k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))) )),
% 35.90/4.94    inference(superposition,[],[f54,f32])).
% 35.90/4.94  fof(f48,plain,(
% 35.90/4.94    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 35.90/4.94    inference(cnf_transformation,[],[f30])).
% 35.90/4.94  fof(f98,plain,(
% 35.90/4.94    ( ! [X0] : (r1_tarski(X0,k1_xboole_0) | k1_xboole_0 != X0) )),
% 35.90/4.94    inference(superposition,[],[f51,f37])).
% 35.90/4.94  fof(f51,plain,(
% 35.90/4.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 35.90/4.94    inference(cnf_transformation,[],[f31])).
% 35.90/4.94  fof(f31,plain,(
% 35.90/4.94    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 35.90/4.94    inference(nnf_transformation,[],[f4])).
% 35.90/4.94  fof(f4,axiom,(
% 35.90/4.94    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 35.90/4.94  fof(f20723,plain,(
% 35.90/4.94    ( ! [X156,X157] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X156,X157)) | ~r1_tarski(X156,sK2) | r1_tarski(sK3,X157) | k1_xboole_0 = sK2) )),
% 35.90/4.94    inference(resolution,[],[f1143,f290])).
% 35.90/4.94  fof(f290,plain,(
% 35.90/4.94    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) | r1_tarski(sK3,X0) | k1_xboole_0 = sK2) )),
% 35.90/4.94    inference(superposition,[],[f58,f32])).
% 35.90/4.94  fof(f58,plain,(
% 35.90/4.94    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 35.90/4.94    inference(cnf_transformation,[],[f24])).
% 35.90/4.94  fof(f24,plain,(
% 35.90/4.94    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 35.90/4.94    inference(ennf_transformation,[],[f15])).
% 35.90/4.94  fof(f15,axiom,(
% 35.90/4.94    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 35.90/4.94  fof(f1143,plain,(
% 35.90/4.94    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k2_zfmisc_1(X0,X3)) | ~r1_tarski(X2,k2_zfmisc_1(X1,X3)) | ~r1_tarski(X1,X0)) )),
% 35.90/4.94    inference(superposition,[],[f207,f82])).
% 35.90/4.94  fof(f82,plain,(
% 35.90/4.94    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) )),
% 35.90/4.94    inference(superposition,[],[f44,f39])).
% 35.90/4.94  fof(f207,plain,(
% 35.90/4.94    ( ! [X17,X15,X18,X16] : (r1_tarski(X18,k2_zfmisc_1(k2_xboole_0(X15,X17),X16)) | ~r1_tarski(X18,k2_zfmisc_1(X17,X16))) )),
% 35.90/4.94    inference(superposition,[],[f56,f54])).
% 35.90/4.94  fof(f28972,plain,(
% 35.90/4.94    sK0 = sK2 | ~r1_tarski(sK3,sK1)),
% 35.90/4.94    inference(backward_demodulation,[],[f25333,f28957])).
% 35.90/4.94  fof(f28957,plain,(
% 35.90/4.94    sK2 = k3_xboole_0(sK0,sK2)),
% 35.90/4.94    inference(subsumption_resolution,[],[f28952,f103])).
% 35.90/4.94  fof(f28952,plain,(
% 35.90/4.94    sK2 = k3_xboole_0(sK0,sK2) | ~r1_tarski(k3_xboole_0(sK0,sK2),sK2)),
% 35.90/4.94    inference(resolution,[],[f28730,f47])).
% 35.90/4.94  fof(f28730,plain,(
% 35.90/4.94    r1_tarski(sK2,k3_xboole_0(sK0,sK2))),
% 35.90/4.94    inference(subsumption_resolution,[],[f28729,f637])).
% 35.90/4.94  fof(f637,plain,(
% 35.90/4.94    k1_xboole_0 != sK3),
% 35.90/4.94    inference(resolution,[],[f611,f98])).
% 35.90/4.94  fof(f611,plain,(
% 35.90/4.94    ~r1_tarski(sK3,k1_xboole_0)),
% 35.90/4.94    inference(subsumption_resolution,[],[f610,f34])).
% 35.90/4.94  fof(f610,plain,(
% 35.90/4.94    k1_xboole_0 = sK1 | ~r1_tarski(sK3,k1_xboole_0)),
% 35.90/4.94    inference(subsumption_resolution,[],[f599,f33])).
% 35.90/4.94  fof(f599,plain,(
% 35.90/4.94    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~r1_tarski(sK3,k1_xboole_0)),
% 35.90/4.94    inference(trivial_inequality_removal,[],[f590])).
% 35.90/4.94  fof(f590,plain,(
% 35.90/4.94    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~r1_tarski(sK3,k1_xboole_0)),
% 35.90/4.94    inference(superposition,[],[f48,f554])).
% 35.90/4.94  fof(f554,plain,(
% 35.90/4.94    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(sK3,k1_xboole_0)),
% 35.90/4.94    inference(subsumption_resolution,[],[f552,f94])).
% 35.90/4.94  fof(f552,plain,(
% 35.90/4.94    ~r1_tarski(sK3,k1_xboole_0) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 35.90/4.94    inference(resolution,[],[f522,f47])).
% 35.90/4.94  fof(f522,plain,(
% 35.90/4.94    r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) | ~r1_tarski(sK3,k1_xboole_0)),
% 35.90/4.94    inference(superposition,[],[f441,f62])).
% 35.90/4.94  fof(f62,plain,(
% 35.90/4.94    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 35.90/4.94    inference(equality_resolution,[],[f50])).
% 35.90/4.94  fof(f50,plain,(
% 35.90/4.94    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 35.90/4.94    inference(cnf_transformation,[],[f30])).
% 35.90/4.94  fof(f441,plain,(
% 35.90/4.94    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) | ~r1_tarski(sK3,X0)) )),
% 35.90/4.94    inference(superposition,[],[f362,f44])).
% 35.90/4.94  fof(f362,plain,(
% 35.90/4.94    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(sK3,X0)))) )),
% 35.90/4.94    inference(superposition,[],[f38,f235])).
% 35.90/4.94  fof(f235,plain,(
% 35.90/4.94    ( ! [X0] : (k2_zfmisc_1(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0))) )),
% 35.90/4.94    inference(superposition,[],[f55,f32])).
% 35.90/4.94  fof(f28729,plain,(
% 35.90/4.94    r1_tarski(sK2,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK3),
% 35.90/4.94    inference(subsumption_resolution,[],[f28596,f60])).
% 35.90/4.94  fof(f28596,plain,(
% 35.90/4.94    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK2,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK3),
% 35.90/4.94    inference(superposition,[],[f276,f28350])).
% 35.90/4.94  fof(f28350,plain,(
% 35.90/4.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)),
% 35.90/4.94    inference(backward_demodulation,[],[f7399,f28337])).
% 35.90/4.94  fof(f28337,plain,(
% 35.90/4.94    sK3 = k3_xboole_0(sK1,sK3)),
% 35.90/4.94    inference(subsumption_resolution,[],[f28332,f103])).
% 35.90/4.94  fof(f28332,plain,(
% 35.90/4.94    sK3 = k3_xboole_0(sK1,sK3) | ~r1_tarski(k3_xboole_0(sK1,sK3),sK3)),
% 35.90/4.94    inference(resolution,[],[f28316,f47])).
% 35.90/4.94  fof(f276,plain,(
% 35.90/4.94    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) | r1_tarski(sK2,X0) | k1_xboole_0 = sK3) )),
% 35.90/4.94    inference(superposition,[],[f57,f32])).
% 35.90/4.94  fof(f57,plain,(
% 35.90/4.94    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 35.90/4.94    inference(cnf_transformation,[],[f24])).
% 35.90/4.94  fof(f25333,plain,(
% 35.90/4.94    sK0 = k3_xboole_0(sK0,sK2) | ~r1_tarski(sK3,sK1)),
% 35.90/4.94    inference(forward_demodulation,[],[f25314,f37])).
% 35.90/4.94  fof(f25314,plain,(
% 35.90/4.94    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) | ~r1_tarski(sK3,sK1)),
% 35.90/4.94    inference(superposition,[],[f43,f25102])).
% 35.90/4.94  fof(f25102,plain,(
% 35.90/4.94    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~r1_tarski(sK3,sK1)),
% 35.90/4.94    inference(resolution,[],[f25052,f125])).
% 35.90/4.94  fof(f125,plain,(
% 35.90/4.94    ( ! [X4,X3] : (~r1_tarski(k2_xboole_0(X3,X4),X4) | k1_xboole_0 = k4_xboole_0(X3,X4)) )),
% 35.90/4.94    inference(superposition,[],[f42,f52])).
% 35.90/4.94  fof(f52,plain,(
% 35.90/4.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 35.90/4.94    inference(cnf_transformation,[],[f31])).
% 35.90/4.94  fof(f42,plain,(
% 35.90/4.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 35.90/4.94    inference(cnf_transformation,[],[f11])).
% 35.90/4.94  fof(f11,axiom,(
% 35.90/4.94    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 35.90/4.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 35.90/4.94  fof(f25052,plain,(
% 35.90/4.94    r1_tarski(k2_xboole_0(sK0,sK2),sK2) | ~r1_tarski(sK3,sK1)),
% 35.90/4.94    inference(resolution,[],[f3894,f672])).
% 35.90/4.94  fof(f672,plain,(
% 35.90/4.94    ( ! [X4,X5,X3] : (r1_tarski(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X5,X4)) | ~r1_tarski(X3,X4)) )),
% 35.90/4.94    inference(superposition,[],[f248,f44])).
% 35.90/4.94  fof(f248,plain,(
% 35.90/4.94    ( ! [X4,X2,X3] : (r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X2,k2_xboole_0(X3,X4)))) )),
% 35.90/4.94    inference(superposition,[],[f38,f55])).
% 35.90/4.94  fof(f3894,plain,(
% 35.90/4.94    ( ! [X16] : (~r1_tarski(k2_zfmisc_1(X16,sK3),k2_zfmisc_1(sK0,sK1)) | r1_tarski(k2_xboole_0(X16,sK2),sK2)) )),
% 35.90/4.94    inference(subsumption_resolution,[],[f3893,f637])).
% 35.90/4.94  fof(f3893,plain,(
% 35.90/4.94    ( ! [X16] : (r1_tarski(k2_xboole_0(X16,sK2),sK2) | k1_xboole_0 = sK3 | ~r1_tarski(k2_zfmisc_1(X16,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 35.90/4.94    inference(subsumption_resolution,[],[f3844,f60])).
% 35.90/4.94  fof(f3844,plain,(
% 35.90/4.94    ( ! [X16] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(k2_xboole_0(X16,sK2),sK2) | k1_xboole_0 = sK3 | ~r1_tarski(k2_zfmisc_1(X16,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 35.90/4.94    inference(superposition,[],[f279,f336])).
% 35.90/4.94  fof(f336,plain,(
% 35.90/4.94    ( ! [X1] : (k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3) | ~r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 35.90/4.94    inference(superposition,[],[f196,f44])).
% 35.90/4.94  fof(f196,plain,(
% 35.90/4.94    ( ! [X0] : (k2_zfmisc_1(k2_xboole_0(X0,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 35.90/4.94    inference(superposition,[],[f54,f32])).
% 35.90/4.94  fof(f279,plain,(
% 35.90/4.94    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1)) | r1_tarski(X0,sK2) | k1_xboole_0 = sK3) )),
% 35.90/4.94    inference(superposition,[],[f57,f32])).
% 35.90/4.94  fof(f35,plain,(
% 35.90/4.94    sK1 != sK3 | sK0 != sK2),
% 35.90/4.94    inference(cnf_transformation,[],[f26])).
% 35.90/4.94  fof(f33486,plain,(
% 35.90/4.94    sK1 = sK3),
% 35.90/4.94    inference(subsumption_resolution,[],[f33485,f28330])).
% 35.90/4.94  fof(f33485,plain,(
% 35.90/4.94    ~r1_tarski(sK3,sK1) | sK1 = sK3),
% 35.90/4.94    inference(subsumption_resolution,[],[f29365,f60])).
% 35.90/4.94  fof(f29365,plain,(
% 35.90/4.94    ~r1_tarski(sK0,sK0) | ~r1_tarski(sK3,sK1) | sK1 = sK3),
% 35.90/4.94    inference(backward_demodulation,[],[f332,f29341])).
% 35.90/4.94  fof(f332,plain,(
% 35.90/4.94    ~r1_tarski(sK3,sK1) | sK1 = sK3 | ~r1_tarski(sK2,sK0)),
% 35.90/4.94    inference(resolution,[],[f300,f47])).
% 35.90/4.94  fof(f300,plain,(
% 35.90/4.94    r1_tarski(sK1,sK3) | ~r1_tarski(sK2,sK0)),
% 35.90/4.94    inference(subsumption_resolution,[],[f296,f33])).
% 35.90/4.94  fof(f296,plain,(
% 35.90/4.94    ~r1_tarski(sK2,sK0) | r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 35.90/4.94    inference(resolution,[],[f268,f58])).
% 35.90/4.94  % SZS output end Proof for theBenchmark
% 35.90/4.94  % (20974)------------------------------
% 35.90/4.94  % (20974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 35.90/4.94  % (20974)Termination reason: Refutation
% 35.90/4.94  
% 35.90/4.94  % (20974)Memory used [KB]: 25585
% 35.90/4.94  % (20974)Time elapsed: 4.441 s
% 35.90/4.94  % (20974)------------------------------
% 35.90/4.94  % (20974)------------------------------
% 35.90/4.95  % (20961)Success in time 4.589 s
%------------------------------------------------------------------------------
