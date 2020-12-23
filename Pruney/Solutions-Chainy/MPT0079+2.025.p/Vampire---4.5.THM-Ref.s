%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:55 EST 2020

% Result     : Theorem 3.19s
% Output     : Refutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 214 expanded)
%              Number of leaves         :   17 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  133 ( 413 expanded)
%              Number of equality atoms :   89 ( 244 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2845,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2844,f33])).

fof(f33,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f2844,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f726,f2843])).

fof(f2843,plain,(
    sK1 = k4_xboole_0(sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f2842])).

fof(f2842,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f2014,f2840])).

fof(f2840,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f2839,f2057])).

fof(f2057,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK3,X3)) ),
    inference(forward_demodulation,[],[f2048,f165])).

fof(f165,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f156,f38])).

fof(f38,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f156,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f49,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f38,f36])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2048,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k3_xboole_0(sK1,k4_xboole_0(sK3,X3)) ),
    inference(superposition,[],[f112,f271])).

fof(f271,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f62,f32])).

fof(f32,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f46,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f112,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k3_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f48,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f2839,plain,(
    k4_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK3,sK2)) ),
    inference(forward_demodulation,[],[f2800,f35])).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f2800,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK3,sK2)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f1584,f59])).

fof(f59,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f38,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1584,plain,(
    ! [X48] : k3_xboole_0(X48,k4_xboole_0(sK3,sK2)) = k4_xboole_0(k4_xboole_0(X48,sK2),k4_xboole_0(X48,k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f977,f30])).

fof(f30,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f977,plain,(
    ! [X14,X12,X13] : k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k2_xboole_0(X13,X14))) = k3_xboole_0(X12,k4_xboole_0(X14,X13)) ),
    inference(backward_demodulation,[],[f141,f974])).

fof(f974,plain,(
    ! [X10,X8,X9] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k4_xboole_0(X10,X9)) ),
    inference(backward_demodulation,[],[f865,f900])).

fof(f900,plain,(
    ! [X6,X4,X5] : k3_xboole_0(X4,k4_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X6,k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f145,f40])).

fof(f145,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7)) ),
    inference(forward_demodulation,[],[f130,f48])).

fof(f130,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k3_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7)) ),
    inference(superposition,[],[f49,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f865,plain,(
    ! [X10,X8,X9] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X10))) ),
    inference(backward_demodulation,[],[f150,f828])).

fof(f828,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f140,f40])).

fof(f140,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X11,k4_xboole_0(X9,X10)) = k2_xboole_0(X11,k4_xboole_0(X9,k2_xboole_0(X10,X11))) ),
    inference(superposition,[],[f43,f49])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f150,plain,(
    ! [X10,X8,X9] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,k2_xboole_0(X9,X10)))) ),
    inference(forward_demodulation,[],[f136,f49])).

fof(f136,plain,(
    ! [X10,X8,X9] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(k4_xboole_0(X8,X9),X10))) ),
    inference(superposition,[],[f49,f41])).

fof(f141,plain,(
    ! [X14,X12,X13] : k3_xboole_0(k4_xboole_0(X12,X13),X14) = k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k2_xboole_0(X13,X14))) ),
    inference(superposition,[],[f41,f49])).

fof(f2014,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | sK1 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f1976,f726])).

fof(f1976,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK2,sK0))
    | sK1 = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f137,f50])).

fof(f50,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f38,f30])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k4_xboole_0(X2,k4_xboole_0(X0,X1))
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(superposition,[],[f47,f49])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f726,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f721,f722])).

fof(f722,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f692,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f692,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f85,f40])).

fof(f85,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X3,X4)) = k2_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f80,f40])).

fof(f80,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f43,f41])).

fof(f721,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(forward_demodulation,[],[f690,f36])).

fof(f690,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f85,f270])).

fof(f270,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f62,f31])).

fof(f31,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:55:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (8432)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (8429)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (8447)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (8449)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (8440)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (8431)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (8428)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (8437)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (8430)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (8455)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (8438)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (8458)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (8453)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (8450)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (8427)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (8442)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (8454)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (8443)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (8445)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (8448)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (8446)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (8451)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (8433)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (8435)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (8436)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (8439)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.57  % (8452)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.58  % (8434)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.58  % (8444)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.58  % (8444)Refutation not found, incomplete strategy% (8444)------------------------------
% 0.21/0.58  % (8444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (8444)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (8444)Memory used [KB]: 10618
% 0.21/0.58  % (8444)Time elapsed: 0.178 s
% 0.21/0.58  % (8444)------------------------------
% 0.21/0.58  % (8444)------------------------------
% 0.21/0.59  % (8456)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.03/0.68  % (8430)Refutation not found, incomplete strategy% (8430)------------------------------
% 2.03/0.68  % (8430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.68  % (8430)Termination reason: Refutation not found, incomplete strategy
% 2.03/0.68  
% 2.03/0.68  % (8430)Memory used [KB]: 6140
% 2.03/0.68  % (8430)Time elapsed: 0.266 s
% 2.03/0.68  % (8430)------------------------------
% 2.03/0.68  % (8430)------------------------------
% 2.62/0.74  % (8473)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.19/0.81  % (8485)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.19/0.82  % (8452)Time limit reached!
% 3.19/0.82  % (8452)------------------------------
% 3.19/0.82  % (8452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.82  % (8452)Termination reason: Time limit
% 3.19/0.82  
% 3.19/0.82  % (8452)Memory used [KB]: 12409
% 3.19/0.82  % (8452)Time elapsed: 0.406 s
% 3.19/0.82  % (8452)------------------------------
% 3.19/0.82  % (8452)------------------------------
% 3.19/0.85  % (8429)Time limit reached!
% 3.19/0.85  % (8429)------------------------------
% 3.19/0.85  % (8429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.85  % (8429)Termination reason: Time limit
% 3.19/0.85  % (8429)Termination phase: Saturation
% 3.19/0.85  
% 3.19/0.85  % (8429)Memory used [KB]: 6780
% 3.19/0.85  % (8429)Time elapsed: 0.420 s
% 3.19/0.85  % (8429)------------------------------
% 3.19/0.85  % (8429)------------------------------
% 3.19/0.85  % (8434)Refutation found. Thanks to Tanya!
% 3.19/0.85  % SZS status Theorem for theBenchmark
% 3.19/0.85  % SZS output start Proof for theBenchmark
% 3.19/0.85  fof(f2845,plain,(
% 3.19/0.85    $false),
% 3.19/0.85    inference(subsumption_resolution,[],[f2844,f33])).
% 3.19/0.85  fof(f33,plain,(
% 3.19/0.85    sK1 != sK2),
% 3.19/0.85    inference(cnf_transformation,[],[f25])).
% 3.19/0.85  fof(f25,plain,(
% 3.19/0.85    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.19/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f24])).
% 3.19/0.85  fof(f24,plain,(
% 3.19/0.85    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 3.19/0.85    introduced(choice_axiom,[])).
% 3.19/0.85  fof(f20,plain,(
% 3.19/0.85    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 3.19/0.85    inference(flattening,[],[f19])).
% 3.19/0.85  fof(f19,plain,(
% 3.19/0.85    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 3.19/0.85    inference(ennf_transformation,[],[f17])).
% 3.19/0.85  fof(f17,negated_conjecture,(
% 3.19/0.85    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.19/0.85    inference(negated_conjecture,[],[f16])).
% 3.19/0.85  fof(f16,conjecture,(
% 3.19/0.85    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 3.19/0.85  fof(f2844,plain,(
% 3.19/0.85    sK1 = sK2),
% 3.19/0.85    inference(backward_demodulation,[],[f726,f2843])).
% 3.19/0.85  fof(f2843,plain,(
% 3.19/0.85    sK1 = k4_xboole_0(sK2,sK0)),
% 3.19/0.85    inference(trivial_inequality_removal,[],[f2842])).
% 3.19/0.85  fof(f2842,plain,(
% 3.19/0.85    k1_xboole_0 != k1_xboole_0 | sK1 = k4_xboole_0(sK2,sK0)),
% 3.19/0.85    inference(backward_demodulation,[],[f2014,f2840])).
% 3.19/0.85  fof(f2840,plain,(
% 3.19/0.85    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 3.19/0.85    inference(forward_demodulation,[],[f2839,f2057])).
% 3.19/0.85  fof(f2057,plain,(
% 3.19/0.85    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK3,X3))) )),
% 3.19/0.85    inference(forward_demodulation,[],[f2048,f165])).
% 3.19/0.85  fof(f165,plain,(
% 3.19/0.85    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 3.19/0.85    inference(forward_demodulation,[],[f156,f38])).
% 3.19/0.85  fof(f38,plain,(
% 3.19/0.85    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.19/0.85    inference(cnf_transformation,[],[f11])).
% 3.19/0.85  fof(f11,axiom,(
% 3.19/0.85    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 3.19/0.85  fof(f156,plain,(
% 3.19/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1)) )),
% 3.19/0.85    inference(superposition,[],[f49,f51])).
% 3.19/0.85  fof(f51,plain,(
% 3.19/0.85    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.19/0.85    inference(superposition,[],[f38,f36])).
% 3.19/0.85  fof(f36,plain,(
% 3.19/0.85    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.19/0.85    inference(cnf_transformation,[],[f5])).
% 3.19/0.85  fof(f5,axiom,(
% 3.19/0.85    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 3.19/0.85  fof(f49,plain,(
% 3.19/0.85    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.19/0.85    inference(cnf_transformation,[],[f10])).
% 3.19/0.85  fof(f10,axiom,(
% 3.19/0.85    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.19/0.85  fof(f2048,plain,(
% 3.19/0.85    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k3_xboole_0(sK1,k4_xboole_0(sK3,X3))) )),
% 3.19/0.85    inference(superposition,[],[f112,f271])).
% 3.19/0.85  fof(f271,plain,(
% 3.19/0.85    k1_xboole_0 = k3_xboole_0(sK3,sK1)),
% 3.19/0.85    inference(resolution,[],[f62,f32])).
% 3.19/0.85  fof(f32,plain,(
% 3.19/0.85    r1_xboole_0(sK3,sK1)),
% 3.19/0.85    inference(cnf_transformation,[],[f25])).
% 3.19/0.85  fof(f62,plain,(
% 3.19/0.85    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 3.19/0.85    inference(resolution,[],[f46,f37])).
% 3.19/0.85  fof(f37,plain,(
% 3.19/0.85    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 3.19/0.85    inference(cnf_transformation,[],[f27])).
% 3.19/0.85  fof(f27,plain,(
% 3.19/0.85    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 3.19/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f26])).
% 3.19/0.85  fof(f26,plain,(
% 3.19/0.85    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 3.19/0.85    introduced(choice_axiom,[])).
% 3.19/0.85  fof(f21,plain,(
% 3.19/0.85    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.19/0.85    inference(ennf_transformation,[],[f4])).
% 3.19/0.85  fof(f4,axiom,(
% 3.19/0.85    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 3.19/0.85  fof(f46,plain,(
% 3.19/0.85    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.19/0.85    inference(cnf_transformation,[],[f29])).
% 3.19/0.85  fof(f29,plain,(
% 3.19/0.85    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.19/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f28])).
% 3.19/0.85  fof(f28,plain,(
% 3.19/0.85    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 3.19/0.85    introduced(choice_axiom,[])).
% 3.19/0.85  fof(f22,plain,(
% 3.19/0.85    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.19/0.85    inference(ennf_transformation,[],[f18])).
% 3.19/0.85  fof(f18,plain,(
% 3.19/0.85    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.19/0.85    inference(rectify,[],[f3])).
% 3.19/0.85  fof(f3,axiom,(
% 3.19/0.85    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 3.19/0.85  fof(f112,plain,(
% 3.19/0.85    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k3_xboole_0(X3,X2),X4)) )),
% 3.19/0.85    inference(superposition,[],[f48,f39])).
% 3.19/0.85  fof(f39,plain,(
% 3.19/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.19/0.85    inference(cnf_transformation,[],[f2])).
% 3.19/0.85  fof(f2,axiom,(
% 3.19/0.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.19/0.85  fof(f48,plain,(
% 3.19/0.85    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.19/0.85    inference(cnf_transformation,[],[f13])).
% 3.19/0.85  fof(f13,axiom,(
% 3.19/0.85    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 3.19/0.85  fof(f2839,plain,(
% 3.19/0.85    k4_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK3,sK2))),
% 3.19/0.85    inference(forward_demodulation,[],[f2800,f35])).
% 3.19/0.85  fof(f35,plain,(
% 3.19/0.85    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.19/0.85    inference(cnf_transformation,[],[f9])).
% 3.19/0.85  fof(f9,axiom,(
% 3.19/0.85    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 3.19/0.85  fof(f2800,plain,(
% 3.19/0.85    k3_xboole_0(sK1,k4_xboole_0(sK3,sK2)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 3.19/0.85    inference(superposition,[],[f1584,f59])).
% 3.19/0.85  fof(f59,plain,(
% 3.19/0.85    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 3.19/0.85    inference(superposition,[],[f38,f40])).
% 3.19/0.85  fof(f40,plain,(
% 3.19/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.19/0.85    inference(cnf_transformation,[],[f1])).
% 3.19/0.85  fof(f1,axiom,(
% 3.19/0.85    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.19/0.85  fof(f1584,plain,(
% 3.19/0.85    ( ! [X48] : (k3_xboole_0(X48,k4_xboole_0(sK3,sK2)) = k4_xboole_0(k4_xboole_0(X48,sK2),k4_xboole_0(X48,k2_xboole_0(sK0,sK1)))) )),
% 3.19/0.85    inference(superposition,[],[f977,f30])).
% 3.19/0.85  fof(f30,plain,(
% 3.19/0.85    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.19/0.85    inference(cnf_transformation,[],[f25])).
% 3.19/0.85  fof(f977,plain,(
% 3.19/0.85    ( ! [X14,X12,X13] : (k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k2_xboole_0(X13,X14))) = k3_xboole_0(X12,k4_xboole_0(X14,X13))) )),
% 3.19/0.85    inference(backward_demodulation,[],[f141,f974])).
% 3.19/0.85  fof(f974,plain,(
% 3.19/0.85    ( ! [X10,X8,X9] : (k3_xboole_0(k4_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k4_xboole_0(X10,X9))) )),
% 3.19/0.85    inference(backward_demodulation,[],[f865,f900])).
% 3.19/0.85  fof(f900,plain,(
% 3.19/0.85    ( ! [X6,X4,X5] : (k3_xboole_0(X4,k4_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X6,k4_xboole_0(X4,X5)))) )),
% 3.19/0.85    inference(superposition,[],[f145,f40])).
% 3.19/0.85  fof(f145,plain,(
% 3.19/0.85    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7))) )),
% 3.19/0.85    inference(forward_demodulation,[],[f130,f48])).
% 3.19/0.85  fof(f130,plain,(
% 3.19/0.85    ( ! [X6,X7,X5] : (k4_xboole_0(k3_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7))) )),
% 3.19/0.85    inference(superposition,[],[f49,f41])).
% 3.19/0.85  fof(f41,plain,(
% 3.19/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.19/0.85    inference(cnf_transformation,[],[f12])).
% 3.19/0.85  fof(f12,axiom,(
% 3.19/0.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.19/0.85  fof(f865,plain,(
% 3.19/0.85    ( ! [X10,X8,X9] : (k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X10)))) )),
% 3.19/0.85    inference(backward_demodulation,[],[f150,f828])).
% 3.19/0.85  fof(f828,plain,(
% 3.19/0.85    ( ! [X4,X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2)))) )),
% 3.19/0.85    inference(superposition,[],[f140,f40])).
% 3.19/0.85  fof(f140,plain,(
% 3.19/0.85    ( ! [X10,X11,X9] : (k2_xboole_0(X11,k4_xboole_0(X9,X10)) = k2_xboole_0(X11,k4_xboole_0(X9,k2_xboole_0(X10,X11)))) )),
% 3.19/0.85    inference(superposition,[],[f43,f49])).
% 3.19/0.85  fof(f43,plain,(
% 3.19/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.19/0.85    inference(cnf_transformation,[],[f8])).
% 3.19/0.85  fof(f8,axiom,(
% 3.19/0.85    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.19/0.85  fof(f150,plain,(
% 3.19/0.85    ( ! [X10,X8,X9] : (k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,k2_xboole_0(X9,X10))))) )),
% 3.19/0.85    inference(forward_demodulation,[],[f136,f49])).
% 3.19/0.85  fof(f136,plain,(
% 3.19/0.85    ( ! [X10,X8,X9] : (k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(k4_xboole_0(X8,X9),X10)))) )),
% 3.19/0.85    inference(superposition,[],[f49,f41])).
% 3.19/0.85  fof(f141,plain,(
% 3.19/0.85    ( ! [X14,X12,X13] : (k3_xboole_0(k4_xboole_0(X12,X13),X14) = k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k2_xboole_0(X13,X14)))) )),
% 3.19/0.85    inference(superposition,[],[f41,f49])).
% 3.19/0.85  fof(f2014,plain,(
% 3.19/0.85    k1_xboole_0 != k4_xboole_0(sK1,sK2) | sK1 = k4_xboole_0(sK2,sK0)),
% 3.19/0.85    inference(forward_demodulation,[],[f1976,f726])).
% 3.19/0.85  fof(f1976,plain,(
% 3.19/0.85    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK2,sK0)) | sK1 = k4_xboole_0(sK2,sK0)),
% 3.19/0.85    inference(superposition,[],[f137,f50])).
% 3.19/0.85  fof(f50,plain,(
% 3.19/0.85    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 3.19/0.85    inference(superposition,[],[f38,f30])).
% 3.19/0.85  fof(f137,plain,(
% 3.19/0.85    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k4_xboole_0(X2,k4_xboole_0(X0,X1)) | k4_xboole_0(X0,X1) = X2) )),
% 3.19/0.85    inference(superposition,[],[f47,f49])).
% 3.19/0.85  fof(f47,plain,(
% 3.19/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 3.19/0.85    inference(cnf_transformation,[],[f23])).
% 3.19/0.85  fof(f23,plain,(
% 3.19/0.85    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 3.19/0.85    inference(ennf_transformation,[],[f7])).
% 3.19/0.85  fof(f7,axiom,(
% 3.19/0.85    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 3.19/0.85  fof(f726,plain,(
% 3.19/0.85    sK2 = k4_xboole_0(sK2,sK0)),
% 3.19/0.85    inference(backward_demodulation,[],[f721,f722])).
% 3.19/0.85  fof(f722,plain,(
% 3.19/0.85    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 3.19/0.85    inference(forward_demodulation,[],[f692,f44])).
% 3.19/0.85  fof(f44,plain,(
% 3.19/0.85    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.19/0.85    inference(cnf_transformation,[],[f14])).
% 3.19/0.85  fof(f14,axiom,(
% 3.19/0.85    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.19/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 3.19/0.85  fof(f692,plain,(
% 3.19/0.85    ( ! [X2,X3] : (k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 3.19/0.85    inference(superposition,[],[f85,f40])).
% 3.19/0.85  fof(f85,plain,(
% 3.19/0.85    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X3,X4)) = k2_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 3.19/0.85    inference(forward_demodulation,[],[f80,f40])).
% 3.19/0.85  fof(f80,plain,(
% 3.19/0.85    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X3,X4))) )),
% 3.19/0.85    inference(superposition,[],[f43,f41])).
% 3.19/0.85  fof(f721,plain,(
% 3.19/0.85    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 3.19/0.85    inference(forward_demodulation,[],[f690,f36])).
% 3.19/0.85  fof(f690,plain,(
% 3.19/0.85    k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 3.19/0.85    inference(superposition,[],[f85,f270])).
% 3.19/0.85  fof(f270,plain,(
% 3.19/0.85    k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 3.19/0.85    inference(resolution,[],[f62,f31])).
% 3.19/0.85  fof(f31,plain,(
% 3.19/0.85    r1_xboole_0(sK2,sK0)),
% 3.19/0.85    inference(cnf_transformation,[],[f25])).
% 3.19/0.85  % SZS output end Proof for theBenchmark
% 3.19/0.85  % (8434)------------------------------
% 3.19/0.85  % (8434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.85  % (8434)Termination reason: Refutation
% 3.19/0.85  
% 3.19/0.85  % (8434)Memory used [KB]: 4605
% 3.19/0.85  % (8434)Time elapsed: 0.434 s
% 3.19/0.85  % (8434)------------------------------
% 3.19/0.85  % (8434)------------------------------
% 3.19/0.85  % (8425)Success in time 0.485 s
%------------------------------------------------------------------------------
