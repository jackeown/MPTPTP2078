%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t44_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:07 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 ( 109 expanded)
%              Number of leaves         :    3 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 442 expanded)
%              Number of equality atoms :   74 ( 441 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(subsumption_resolution,[],[f200,f77])).

fof(f77,plain,(
    k1_tarski(sK0) = sK1 ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X1] :
      ( k1_tarski(sK0) != k1_tarski(X1)
      | k1_tarski(X1) = sK1 ) ),
    inference(subsumption_resolution,[],[f49,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t44_zfmisc_1.p',t44_zfmisc_1)).

fof(f49,plain,(
    ! [X1] :
      ( k1_tarski(sK0) != k1_tarski(X1)
      | k1_xboole_0 = sK1
      | k1_tarski(X1) = sK1 ) ),
    inference(subsumption_resolution,[],[f41,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X1] :
      ( k1_tarski(sK0) != k1_tarski(X1)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_tarski(X1) = sK1 ) ),
    inference(superposition,[],[f32,f21])).

fof(f21,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X1
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t44_zfmisc_1.p',t43_zfmisc_1)).

fof(f200,plain,(
    k1_tarski(sK0) != sK1 ),
    inference(subsumption_resolution,[],[f178,f22])).

fof(f22,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f178,plain,
    ( sK1 = sK2
    | k1_tarski(sK0) != sK1 ),
    inference(superposition,[],[f81,f77])).

fof(f81,plain,(
    ! [X2] :
      ( k1_tarski(X2) = sK2
      | k1_tarski(X2) != sK1 ) ),
    inference(backward_demodulation,[],[f77,f52])).

fof(f52,plain,(
    ! [X2] :
      ( k1_tarski(sK0) != k1_tarski(X2)
      | k1_tarski(X2) = sK2 ) ),
    inference(subsumption_resolution,[],[f51,f23])).

fof(f51,plain,(
    ! [X2] :
      ( k1_tarski(sK0) != k1_tarski(X2)
      | k1_xboole_0 = sK1
      | k1_tarski(X2) = sK2 ) ),
    inference(subsumption_resolution,[],[f42,f24])).

fof(f42,plain,(
    ! [X2] :
      ( k1_tarski(sK0) != k1_tarski(X2)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_tarski(X2) = sK2 ) ),
    inference(superposition,[],[f33,f21])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
