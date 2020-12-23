%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0898+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:51 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   22 (  90 expanded)
%              Number of leaves         :    3 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :   74 ( 301 expanded)
%              Number of equality atoms :   73 ( 300 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(subsumption_resolution,[],[f31,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f10,f21])).

fof(f21,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f20,f10])).

fof(f20,plain,
    ( k1_xboole_0 = sK1
    | sK0 = sK1 ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK0,sK0,sK0)
      | k1_xboole_0 = sK1
      | sK1 = X0 ) ),
    inference(duplicate_literal_removal,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK0,sK0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1
      | sK1 = X0 ) ),
    inference(superposition,[],[f11,f9])).

fof(f9,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( sK0 != sK1
    & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) )
   => ( sK0 != sK1
      & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f11,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
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
    inference(flattening,[],[f5])).

fof(f5,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f10,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    k1_xboole_0 = sK0 ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_zfmisc_1(X4,X5,X6,X7) != k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | sK0 = X4 ) ),
    inference(subsumption_resolution,[],[f28,f24])).

fof(f28,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_zfmisc_1(X4,X5,X6,X7) != k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = sK0
      | sK0 = X4 ) ),
    inference(duplicate_literal_removal,[],[f27])).

fof(f27,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_zfmisc_1(X4,X5,X6,X7) != k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0
      | sK0 = X4 ) ),
    inference(superposition,[],[f11,f23])).

fof(f23,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f9,f21])).

%------------------------------------------------------------------------------
