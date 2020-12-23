%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0877+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:49 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 238 expanded)
%              Number of leaves         :    4 (  54 expanded)
%              Depth                    :   28
%              Number of atoms          :  188 (1157 expanded)
%              Number of equality atoms :  187 (1156 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f334,plain,(
    $false ),
    inference(subsumption_resolution,[],[f333,f14])).

fof(f14,plain,(
    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
      & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f333,plain,(
    k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f326,f25])).

fof(f25,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X1,X2) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f326,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(k1_xboole_0,sK4,sK5) ),
    inference(backward_demodulation,[],[f13,f325])).

fof(f325,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f324,f14])).

fof(f324,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f314,f24])).

fof(f24,plain,(
    ! [X2,X0] : k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f314,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,k1_xboole_0,sK5)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f13,f311])).

fof(f311,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f310,f14])).

fof(f310,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f297,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f297,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f13,f295])).

fof(f295,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_subsumption,[],[f15,f80,f142,f275])).

fof(f275,plain,
    ( sK2 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5 ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X17,X15,X16] :
      ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4
      | k1_xboole_0 = sK3
      | sK5 = X17 ) ),
    inference(superposition,[],[f22,f13])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f142,plain,
    ( sK1 = sK4
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f141,f14])).

fof(f141,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | sK1 = sK4 ),
    inference(forward_demodulation,[],[f138,f23])).

fof(f138,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK4,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | sK1 = sK4 ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK4,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK1 = sK4 ),
    inference(superposition,[],[f81,f130])).

fof(f130,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK1 = sK4 ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X17,X15,X16] :
      ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4
      | k1_xboole_0 = sK3
      | sK4 = X16 ) ),
    inference(superposition,[],[f21,f13])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK4,sK5)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f13,f80])).

fof(f80,plain,
    ( sK0 = sK3
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f79,f14])).

fof(f79,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK3
    | sK0 = sK3 ),
    inference(forward_demodulation,[],[f78,f24])).

fof(f78,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,k1_xboole_0,sK5)
    | k1_xboole_0 = sK3
    | sK0 = sK3 ),
    inference(superposition,[],[f13,f77])).

fof(f77,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK0 = sK3 ),
    inference(subsumption_resolution,[],[f76,f14])).

fof(f76,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK0 = sK3 ),
    inference(forward_demodulation,[],[f75,f23])).

fof(f75,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,k1_xboole_0)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK0 = sK3 ),
    inference(superposition,[],[f13,f70])).

fof(f70,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK0 = sK3 ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X17,X15,X16] :
      ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4
      | k1_xboole_0 = sK3
      | sK3 = X15 ) ),
    inference(superposition,[],[f20,f13])).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
