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
% DateTime   : Thu Dec  3 12:59:14 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 831 expanded)
%              Number of leaves         :    6 ( 188 expanded)
%              Depth                    :   40
%              Number of atoms          :  305 (3623 expanded)
%              Number of equality atoms :  304 (3622 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(subsumption_resolution,[],[f249,f47])).

fof(f47,plain,(
    ! [X4,X5,X3] : k1_xboole_0 = k4_zfmisc_1(X3,k1_xboole_0,X4,X5) ),
    inference(forward_demodulation,[],[f41,f28])).

fof(f28,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f41,plain,(
    ! [X4,X5,X3] : k4_zfmisc_1(X3,k1_xboole_0,X4,X5) = k2_zfmisc_1(k1_xboole_0,X5) ),
    inference(superposition,[],[f22,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f29,f28])).

fof(f29,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_xboole_0,X1) = k3_zfmisc_1(X0,k1_xboole_0,X1) ),
    inference(superposition,[],[f21,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f249,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f16,f247])).

fof(f247,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f238,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_zfmisc_1(X0,X1,k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f40,f28])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_xboole_0,X2) = k4_zfmisc_1(X0,X1,k1_xboole_0,X2) ),
    inference(superposition,[],[f22,f32])).

fof(f32,plain,(
    ! [X4,X3] : k1_xboole_0 = k3_zfmisc_1(X3,X4,k1_xboole_0) ),
    inference(superposition,[],[f21,f27])).

fof(f238,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,k1_xboole_0,sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f16,f232])).

fof(f232,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f223,f42])).

fof(f42,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k4_zfmisc_1(X4,X5,X6,k1_xboole_0) ),
    inference(superposition,[],[f22,f27])).

fof(f223,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f16,f220])).

fof(f220,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f219,f84])).

fof(f84,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f83,f16])).

fof(f83,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f82,f49])).

fof(f49,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k4_zfmisc_1(k1_xboole_0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f48,f28])).

fof(f48,plain,(
    ! [X2,X3,X1] : k2_zfmisc_1(k1_xboole_0,X3) = k4_zfmisc_1(k1_xboole_0,X1,X2,X3) ),
    inference(superposition,[],[f22,f35])).

fof(f35,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X2,X3) ),
    inference(forward_demodulation,[],[f30,f28])).

fof(f30,plain,(
    ! [X2,X3] : k3_zfmisc_1(k1_xboole_0,X2,X3) = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(superposition,[],[f21,f28])).

fof(f82,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(k1_xboole_0,sK5,sK6,sK7)
    | k1_xboole_0 != sK0 ),
    inference(superposition,[],[f15,f77])).

fof(f77,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f76,f16])).

fof(f76,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK4
    | k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f75,f47])).

fof(f75,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,k1_xboole_0,sK6,sK7)
    | k1_xboole_0 = sK4
    | k1_xboole_0 != sK0 ),
    inference(superposition,[],[f15,f72])).

fof(f72,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f71,f16])).

fof(f71,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f70,f46])).

fof(f70,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,k1_xboole_0,sK7)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 != sK0 ),
    inference(superposition,[],[f15,f66])).

fof(f66,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f65,f16])).

fof(f65,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f64,f42])).

fof(f64,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,k1_xboole_0)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 != sK0 ),
    inference(superposition,[],[f15,f59])).

fof(f59,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 != sK0 ),
    inference(equality_factoring,[],[f54])).

fof(f54,plain,
    ( sK0 = sK4
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK7 ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4
      | sK4 = X0 ) ),
    inference(superposition,[],[f23,f15])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f15,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f219,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(trivial_inequality_removal,[],[f214])).

fof(f214,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f189,f74])).

fof(f74,plain,
    ( sK0 = sK4
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK4 = X0 ) ),
    inference(superposition,[],[f23,f15])).

fof(f189,plain,(
    sK0 != sK4 ),
    inference(subsumption_resolution,[],[f180,f47])).

fof(f180,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,k1_xboole_0,sK2,sK3)
    | sK0 != sK4 ),
    inference(superposition,[],[f16,f172])).

fof(f172,plain,
    ( k1_xboole_0 = sK1
    | sK0 != sK4 ),
    inference(subsumption_resolution,[],[f163,f46])).

fof(f163,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,k1_xboole_0,sK3)
    | k1_xboole_0 = sK1
    | sK0 != sK4 ),
    inference(superposition,[],[f16,f150])).

fof(f150,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | sK0 != sK4 ),
    inference(subsumption_resolution,[],[f141,f42])).

fof(f141,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,k1_xboole_0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | sK0 != sK4 ),
    inference(superposition,[],[f16,f122])).

fof(f122,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | sK0 != sK4 ),
    inference(subsumption_resolution,[],[f121,f87])).

fof(f87,plain,
    ( sK1 = sK5
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f86,f84])).

fof(f86,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK1 = sK5 ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK5 = X1 ) ),
    inference(superposition,[],[f24,f15])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X5 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f121,plain,
    ( sK1 != sK5
    | sK0 != sK4
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f118,f97])).

fof(f97,plain,
    ( sK2 = sK6
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f96,f84])).

fof(f96,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK2 = sK6 ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK6 = X2 ) ),
    inference(superposition,[],[f25,f15])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X2 = X6 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f118,plain,
    ( sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,
    ( sK3 != sK3
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f17,f113])).

fof(f113,plain,
    ( sK3 = sK7
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f112,f84])).

fof(f112,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = sK7 ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK7 = X3 ) ),
    inference(superposition,[],[f26,f15])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X3 = X7 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f12])).

fof(f16,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).
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
% 0.13/0.35  % DateTime   : Tue Dec  1 11:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (11985)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.25/0.54  % (12000)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.25/0.54  % (11981)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.25/0.54  % (11989)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.25/0.54  % (12002)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.25/0.54  % (11983)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.25/0.54  % (11994)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.25/0.54  % (12004)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.25/0.54  % (11980)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.25/0.54  % (11990)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.25/0.55  % (11984)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.25/0.55  % (11989)Refutation found. Thanks to Tanya!
% 1.25/0.55  % SZS status Theorem for theBenchmark
% 1.25/0.55  % SZS output start Proof for theBenchmark
% 1.25/0.55  fof(f265,plain,(
% 1.25/0.55    $false),
% 1.25/0.55    inference(subsumption_resolution,[],[f249,f47])).
% 1.25/0.55  fof(f47,plain,(
% 1.25/0.55    ( ! [X4,X5,X3] : (k1_xboole_0 = k4_zfmisc_1(X3,k1_xboole_0,X4,X5)) )),
% 1.25/0.55    inference(forward_demodulation,[],[f41,f28])).
% 1.25/0.55  fof(f28,plain,(
% 1.25/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.25/0.55    inference(equality_resolution,[],[f19])).
% 1.25/0.55  fof(f19,plain,(
% 1.25/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.25/0.55    inference(cnf_transformation,[],[f14])).
% 1.25/0.55  fof(f14,plain,(
% 1.25/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.25/0.55    inference(flattening,[],[f13])).
% 1.25/0.55  fof(f13,plain,(
% 1.25/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.25/0.55    inference(nnf_transformation,[],[f1])).
% 1.25/0.55  fof(f1,axiom,(
% 1.25/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.25/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.25/0.55  fof(f41,plain,(
% 1.25/0.55    ( ! [X4,X5,X3] : (k4_zfmisc_1(X3,k1_xboole_0,X4,X5) = k2_zfmisc_1(k1_xboole_0,X5)) )),
% 1.25/0.55    inference(superposition,[],[f22,f34])).
% 1.25/0.55  fof(f34,plain,(
% 1.25/0.55    ( ! [X0,X1] : (k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X1)) )),
% 1.25/0.55    inference(forward_demodulation,[],[f29,f28])).
% 1.25/0.55  fof(f29,plain,(
% 1.25/0.55    ( ! [X0,X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k3_zfmisc_1(X0,k1_xboole_0,X1)) )),
% 1.25/0.55    inference(superposition,[],[f21,f27])).
% 1.25/0.55  fof(f27,plain,(
% 1.25/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.25/0.55    inference(equality_resolution,[],[f20])).
% 1.25/0.55  fof(f20,plain,(
% 1.25/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.25/0.55    inference(cnf_transformation,[],[f14])).
% 1.25/0.55  fof(f21,plain,(
% 1.25/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.25/0.55    inference(cnf_transformation,[],[f2])).
% 1.25/0.55  fof(f2,axiom,(
% 1.25/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.25/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.25/0.55  fof(f22,plain,(
% 1.25/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.25/0.55    inference(cnf_transformation,[],[f3])).
% 1.25/0.55  fof(f3,axiom,(
% 1.25/0.55    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.25/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.25/0.55  fof(f249,plain,(
% 1.25/0.55    k1_xboole_0 != k4_zfmisc_1(sK0,k1_xboole_0,sK2,sK3)),
% 1.25/0.55    inference(backward_demodulation,[],[f16,f247])).
% 1.25/0.55  fof(f247,plain,(
% 1.25/0.55    k1_xboole_0 = sK1),
% 1.25/0.55    inference(subsumption_resolution,[],[f238,f46])).
% 1.25/0.55  fof(f46,plain,(
% 1.25/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,k1_xboole_0,X2)) )),
% 1.25/0.55    inference(forward_demodulation,[],[f40,f28])).
% 1.25/0.55  fof(f40,plain,(
% 1.25/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_xboole_0,X2) = k4_zfmisc_1(X0,X1,k1_xboole_0,X2)) )),
% 1.25/0.55    inference(superposition,[],[f22,f32])).
% 1.25/0.55  fof(f32,plain,(
% 1.25/0.55    ( ! [X4,X3] : (k1_xboole_0 = k3_zfmisc_1(X3,X4,k1_xboole_0)) )),
% 1.25/0.55    inference(superposition,[],[f21,f27])).
% 1.25/0.55  fof(f238,plain,(
% 1.25/0.55    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,k1_xboole_0,sK3) | k1_xboole_0 = sK1),
% 1.25/0.55    inference(superposition,[],[f16,f232])).
% 1.25/0.55  fof(f232,plain,(
% 1.25/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.25/0.55    inference(subsumption_resolution,[],[f223,f42])).
% 1.25/0.55  fof(f42,plain,(
% 1.25/0.55    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_zfmisc_1(X4,X5,X6,k1_xboole_0)) )),
% 1.25/0.55    inference(superposition,[],[f22,f27])).
% 1.25/0.55  fof(f223,plain,(
% 1.25/0.55    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 1.25/0.55    inference(superposition,[],[f16,f220])).
% 1.25/0.55  fof(f220,plain,(
% 1.25/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 1.25/0.55    inference(subsumption_resolution,[],[f219,f84])).
% 1.25/0.55  fof(f84,plain,(
% 1.25/0.55    k1_xboole_0 != sK0),
% 1.25/0.55    inference(subsumption_resolution,[],[f83,f16])).
% 1.25/0.55  fof(f83,plain,(
% 1.25/0.55    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK0),
% 1.25/0.55    inference(forward_demodulation,[],[f82,f49])).
% 1.25/0.55  fof(f49,plain,(
% 1.25/0.55    ( ! [X2,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(k1_xboole_0,X1,X2,X3)) )),
% 1.25/0.55    inference(forward_demodulation,[],[f48,f28])).
% 1.25/0.55  fof(f48,plain,(
% 1.25/0.55    ( ! [X2,X3,X1] : (k2_zfmisc_1(k1_xboole_0,X3) = k4_zfmisc_1(k1_xboole_0,X1,X2,X3)) )),
% 1.25/0.55    inference(superposition,[],[f22,f35])).
% 1.25/0.55  fof(f35,plain,(
% 1.25/0.55    ( ! [X2,X3] : (k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X2,X3)) )),
% 1.25/0.55    inference(forward_demodulation,[],[f30,f28])).
% 1.25/0.55  fof(f30,plain,(
% 1.25/0.55    ( ! [X2,X3] : (k3_zfmisc_1(k1_xboole_0,X2,X3) = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 1.25/0.55    inference(superposition,[],[f21,f28])).
% 1.25/0.55  fof(f82,plain,(
% 1.25/0.55    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(k1_xboole_0,sK5,sK6,sK7) | k1_xboole_0 != sK0),
% 1.25/0.55    inference(superposition,[],[f15,f77])).
% 1.25/0.55  fof(f77,plain,(
% 1.25/0.55    k1_xboole_0 = sK4 | k1_xboole_0 != sK0),
% 1.25/0.55    inference(subsumption_resolution,[],[f76,f16])).
% 1.25/0.55  fof(f76,plain,(
% 1.25/0.55    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK4 | k1_xboole_0 != sK0),
% 1.25/0.55    inference(forward_demodulation,[],[f75,f47])).
% 1.25/0.55  fof(f75,plain,(
% 1.25/0.55    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,k1_xboole_0,sK6,sK7) | k1_xboole_0 = sK4 | k1_xboole_0 != sK0),
% 1.25/0.55    inference(superposition,[],[f15,f72])).
% 1.25/0.55  fof(f72,plain,(
% 1.25/0.55    k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 != sK0),
% 1.25/0.55    inference(subsumption_resolution,[],[f71,f16])).
% 1.25/0.55  fof(f71,plain,(
% 1.25/0.55    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 != sK0),
% 1.25/0.55    inference(forward_demodulation,[],[f70,f46])).
% 1.25/0.55  fof(f70,plain,(
% 1.25/0.55    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,k1_xboole_0,sK7) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 != sK0),
% 1.25/0.55    inference(superposition,[],[f15,f66])).
% 1.25/0.55  fof(f66,plain,(
% 1.25/0.55    k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 != sK0),
% 1.25/0.55    inference(subsumption_resolution,[],[f65,f16])).
% 1.25/0.55  fof(f65,plain,(
% 1.25/0.55    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 != sK0),
% 1.25/0.55    inference(forward_demodulation,[],[f64,f42])).
% 1.25/0.55  fof(f64,plain,(
% 1.25/0.55    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,k1_xboole_0) | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 != sK0),
% 1.25/0.55    inference(superposition,[],[f15,f59])).
% 1.25/0.55  fof(f59,plain,(
% 1.25/0.55    k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 != sK0),
% 1.25/0.55    inference(equality_factoring,[],[f54])).
% 1.25/0.55  fof(f54,plain,(
% 1.25/0.55    sK0 = sK4 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK7),
% 1.25/0.55    inference(equality_resolution,[],[f50])).
% 1.25/0.55  fof(f50,plain,(
% 1.25/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK4 = X0) )),
% 1.25/0.55    inference(superposition,[],[f23,f15])).
% 1.25/0.55  fof(f23,plain,(
% 1.25/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X4) )),
% 1.25/0.55    inference(cnf_transformation,[],[f10])).
% 1.25/0.55  fof(f10,plain,(
% 1.25/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7))),
% 1.25/0.55    inference(flattening,[],[f9])).
% 1.25/0.55  fof(f9,plain,(
% 1.25/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7))),
% 1.25/0.55    inference(ennf_transformation,[],[f4])).
% 1.25/0.55  fof(f4,axiom,(
% 1.25/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.25/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).
% 1.25/0.55  fof(f15,plain,(
% 1.25/0.55    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.25/0.55    inference(cnf_transformation,[],[f12])).
% 1.25/0.55  fof(f12,plain,(
% 1.25/0.55    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.25/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f11])).
% 1.25/0.55  fof(f11,plain,(
% 1.25/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.25/0.55    introduced(choice_axiom,[])).
% 1.25/0.55  fof(f8,plain,(
% 1.25/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.25/0.55    inference(flattening,[],[f7])).
% 1.25/0.55  fof(f7,plain,(
% 1.25/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.25/0.55    inference(ennf_transformation,[],[f6])).
% 1.25/0.55  fof(f6,negated_conjecture,(
% 1.25/0.55    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.25/0.55    inference(negated_conjecture,[],[f5])).
% 1.25/0.55  fof(f5,conjecture,(
% 1.25/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.25/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).
% 1.25/0.55  fof(f219,plain,(
% 1.25/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK3),
% 1.25/0.55    inference(trivial_inequality_removal,[],[f214])).
% 1.25/0.55  fof(f214,plain,(
% 1.25/0.55    sK0 != sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK3),
% 1.25/0.55    inference(superposition,[],[f189,f74])).
% 1.25/0.55  fof(f74,plain,(
% 1.25/0.55    sK0 = sK4 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK3),
% 1.25/0.55    inference(equality_resolution,[],[f51])).
% 1.25/0.55  fof(f51,plain,(
% 1.25/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sK4 = X0) )),
% 1.25/0.55    inference(superposition,[],[f23,f15])).
% 1.25/0.55  fof(f189,plain,(
% 1.25/0.55    sK0 != sK4),
% 1.25/0.55    inference(subsumption_resolution,[],[f180,f47])).
% 1.25/0.55  fof(f180,plain,(
% 1.25/0.55    k1_xboole_0 != k4_zfmisc_1(sK0,k1_xboole_0,sK2,sK3) | sK0 != sK4),
% 1.25/0.55    inference(superposition,[],[f16,f172])).
% 1.25/0.55  fof(f172,plain,(
% 1.25/0.55    k1_xboole_0 = sK1 | sK0 != sK4),
% 1.25/0.55    inference(subsumption_resolution,[],[f163,f46])).
% 1.25/0.55  fof(f163,plain,(
% 1.25/0.55    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,k1_xboole_0,sK3) | k1_xboole_0 = sK1 | sK0 != sK4),
% 1.25/0.55    inference(superposition,[],[f16,f150])).
% 1.25/0.55  fof(f150,plain,(
% 1.25/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | sK0 != sK4),
% 1.25/0.55    inference(subsumption_resolution,[],[f141,f42])).
% 1.25/0.55  fof(f141,plain,(
% 1.25/0.55    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,k1_xboole_0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | sK0 != sK4),
% 1.25/0.55    inference(superposition,[],[f16,f122])).
% 1.25/0.55  fof(f122,plain,(
% 1.25/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | sK0 != sK4),
% 1.25/0.55    inference(subsumption_resolution,[],[f121,f87])).
% 1.25/0.55  fof(f87,plain,(
% 1.25/0.55    sK1 = sK5 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 1.25/0.55    inference(subsumption_resolution,[],[f86,f84])).
% 1.25/0.55  fof(f86,plain,(
% 1.25/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK1 = sK5),
% 1.25/0.55    inference(equality_resolution,[],[f56])).
% 1.25/0.55  fof(f56,plain,(
% 1.25/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sK5 = X1) )),
% 1.25/0.55    inference(superposition,[],[f24,f15])).
% 1.25/0.55  fof(f24,plain,(
% 1.25/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X5) )),
% 1.25/0.55    inference(cnf_transformation,[],[f10])).
% 1.25/0.55  fof(f121,plain,(
% 1.25/0.55    sK1 != sK5 | sK0 != sK4 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 1.25/0.55    inference(subsumption_resolution,[],[f118,f97])).
% 1.25/0.55  fof(f97,plain,(
% 1.25/0.55    sK2 = sK6 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 1.25/0.55    inference(subsumption_resolution,[],[f96,f84])).
% 1.25/0.55  fof(f96,plain,(
% 1.25/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK2 = sK6),
% 1.25/0.55    inference(equality_resolution,[],[f61])).
% 1.25/0.55  fof(f61,plain,(
% 1.25/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sK6 = X2) )),
% 1.25/0.55    inference(superposition,[],[f25,f15])).
% 1.25/0.55  fof(f25,plain,(
% 1.25/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X2 = X6) )),
% 1.25/0.55    inference(cnf_transformation,[],[f10])).
% 1.25/0.55  fof(f118,plain,(
% 1.25/0.55    sK2 != sK6 | sK1 != sK5 | sK0 != sK4 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 1.25/0.55    inference(trivial_inequality_removal,[],[f116])).
% 1.25/0.55  fof(f116,plain,(
% 1.25/0.55    sK3 != sK3 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 1.25/0.55    inference(superposition,[],[f17,f113])).
% 1.25/0.55  fof(f113,plain,(
% 1.25/0.55    sK3 = sK7 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 1.25/0.55    inference(subsumption_resolution,[],[f112,f84])).
% 1.25/0.55  fof(f112,plain,(
% 1.25/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = sK7),
% 1.25/0.55    inference(equality_resolution,[],[f68])).
% 1.25/0.55  fof(f68,plain,(
% 1.25/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sK7 = X3) )),
% 1.25/0.55    inference(superposition,[],[f26,f15])).
% 1.25/0.55  fof(f26,plain,(
% 1.25/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X3 = X7) )),
% 1.25/0.55    inference(cnf_transformation,[],[f10])).
% 1.25/0.55  fof(f17,plain,(
% 1.25/0.55    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 1.25/0.55    inference(cnf_transformation,[],[f12])).
% 1.25/0.55  fof(f16,plain,(
% 1.25/0.55    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 1.25/0.55    inference(cnf_transformation,[],[f12])).
% 1.25/0.55  % SZS output end Proof for theBenchmark
% 1.25/0.55  % (11989)------------------------------
% 1.25/0.55  % (11989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.55  % (11989)Termination reason: Refutation
% 1.25/0.55  
% 1.25/0.55  % (11989)Memory used [KB]: 1791
% 1.25/0.55  % (11989)Time elapsed: 0.134 s
% 1.25/0.55  % (11989)------------------------------
% 1.25/0.55  % (11989)------------------------------
% 1.25/0.55  % (11979)Success in time 0.188 s
%------------------------------------------------------------------------------
