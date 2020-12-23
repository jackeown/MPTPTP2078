%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:08 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  101 (2386 expanded)
%              Number of leaves         :   13 ( 685 expanded)
%              Depth                    :   32
%              Number of atoms          :  270 (9414 expanded)
%              Number of equality atoms :  119 (7924 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f858,plain,(
    $false ),
    inference(subsumption_resolution,[],[f853,f734])).

fof(f734,plain,(
    ! [X1] : ~ r1_xboole_0(k2_xboole_0(X1,sK2),sK2) ),
    inference(resolution,[],[f727,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f727,plain,(
    ! [X1] : ~ r1_xboole_0(sK2,k2_xboole_0(X1,sK2)) ),
    inference(resolution,[],[f724,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f724,plain,(
    ~ r1_xboole_0(sK2,sK2) ),
    inference(subsumption_resolution,[],[f720,f629])).

fof(f629,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f626,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f626,plain,(
    ~ r1_tarski(k1_xboole_0,sK2) ),
    inference(trivial_inequality_removal,[],[f625])).

fof(f625,plain,
    ( sK2 != sK2
    | ~ r1_tarski(k1_xboole_0,sK2) ),
    inference(superposition,[],[f612,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f612,plain,(
    sK2 != k2_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f587,f454])).

fof(f454,plain,(
    k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f65,f450])).

fof(f450,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f448,f182])).

fof(f182,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f83,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f83,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
      | k2_xboole_0(sK1,sK2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f73,f65])).

fof(f73,plain,(
    ! [X0] :
      ( k2_xboole_0(sK1,sK2) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(sK0,sK0)) ) ),
    inference(superposition,[],[f65,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f43,f49,f49])).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f448,plain,
    ( sK1 != k2_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f345,f65])).

fof(f345,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f297])).

fof(f297,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 != k2_tarski(sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f62,f293])).

fof(f293,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f285,f47])).

fof(f285,plain,
    ( r1_xboole_0(sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f260,f54])).

fof(f260,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f246,f55])).

fof(f246,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f244,f74])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | r1_xboole_0(k2_xboole_0(sK1,sK2),X0) ) ),
    inference(superposition,[],[f69,f65])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f244,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f194,f206])).

fof(f206,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f191,f168])).

fof(f168,plain,
    ( sK1 != sK2
    | ~ r1_tarski(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f167])).

fof(f167,plain,
    ( sK1 != sK2
    | sK2 != sK2
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f124,f50])).

fof(f124,plain,
    ( sK1 != k2_xboole_0(sK1,sK2)
    | sK2 != k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f64,f65])).

fof(f64,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | sK1 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f40,f49,f49])).

fof(f40,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f191,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f182,f50])).

fof(f194,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | ~ r2_hidden(sK0,X0)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f82,f182])).

fof(f82,plain,(
    ! [X5] :
      ( r1_tarski(k2_xboole_0(sK1,sK2),X5)
      | ~ r2_hidden(sK0,X5) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X5] :
      ( r1_tarski(k2_xboole_0(sK1,sK2),X5)
      | ~ r2_hidden(sK0,X5)
      | ~ r2_hidden(sK0,X5) ) ),
    inference(superposition,[],[f58,f65])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f62,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f42,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f39,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f587,plain,(
    sK2 != k2_tarski(sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f452])).

fof(f452,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK2 != k2_tarski(sK0,sK0) ),
    inference(backward_demodulation,[],[f63,f450])).

fof(f63,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f41,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f720,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | r1_tarski(sK2,sK2) ),
    inference(resolution,[],[f634,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f634,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,sK2),X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f627,f47])).

fof(f627,plain,(
    r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0) ),
    inference(resolution,[],[f626,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f853,plain,(
    r1_xboole_0(k2_xboole_0(k1_xboole_0,sK2),sK2) ),
    inference(resolution,[],[f846,f455])).

fof(f455,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | r1_xboole_0(k2_xboole_0(k1_xboole_0,sK2),X0) ) ),
    inference(backward_demodulation,[],[f74,f450])).

fof(f846,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f845,f459])).

fof(f459,plain,(
    ! [X5] :
      ( r1_tarski(k2_xboole_0(k1_xboole_0,sK2),X5)
      | ~ r2_hidden(sK0,X5) ) ),
    inference(backward_demodulation,[],[f82,f450])).

fof(f845,plain,(
    ~ r1_tarski(k2_xboole_0(k1_xboole_0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f842,f627])).

fof(f842,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_xboole_0,sK2),sK2)
    | ~ r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0) ),
    inference(resolution,[],[f636,f461])).

fof(f461,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_xboole_0(k1_xboole_0,sK2))
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f84,f450])).

fof(f84,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_xboole_0(sK1,sK2))
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f77,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    r1_tarski(k1_xboole_0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f71,f65])).

fof(f71,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f636,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(k1_xboole_0,sK2),X0)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f628,f59])).

fof(f628,plain,(
    ~ r2_hidden(sK3(k1_xboole_0,sK2),sK2) ),
    inference(resolution,[],[f626,f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:10:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (20397)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (20413)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (20391)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (20405)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.57  % (20399)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (20407)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (20395)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (20393)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.58  % (20396)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.58  % (20399)Refutation not found, incomplete strategy% (20399)------------------------------
% 0.22/0.58  % (20399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (20413)Refutation not found, incomplete strategy% (20413)------------------------------
% 1.56/0.58  % (20413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (20413)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (20413)Memory used [KB]: 10874
% 1.56/0.58  % (20413)Time elapsed: 0.140 s
% 1.56/0.58  % (20413)------------------------------
% 1.56/0.58  % (20413)------------------------------
% 1.56/0.59  % (20394)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.56/0.59  % (20391)Refutation found. Thanks to Tanya!
% 1.56/0.59  % SZS status Theorem for theBenchmark
% 1.56/0.59  % (20399)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.59  
% 1.56/0.59  % (20399)Memory used [KB]: 10746
% 1.56/0.59  % (20399)Time elapsed: 0.149 s
% 1.56/0.59  % (20399)------------------------------
% 1.56/0.59  % (20399)------------------------------
% 1.56/0.59  % (20414)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.56/0.60  % (20393)Refutation not found, incomplete strategy% (20393)------------------------------
% 1.56/0.60  % (20393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.60  % (20393)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.60  
% 1.56/0.60  % (20393)Memory used [KB]: 10746
% 1.56/0.60  % (20393)Time elapsed: 0.162 s
% 1.56/0.60  % (20393)------------------------------
% 1.56/0.60  % (20393)------------------------------
% 1.56/0.60  % SZS output start Proof for theBenchmark
% 1.56/0.60  fof(f858,plain,(
% 1.56/0.60    $false),
% 1.56/0.60    inference(subsumption_resolution,[],[f853,f734])).
% 1.56/0.60  fof(f734,plain,(
% 1.56/0.60    ( ! [X1] : (~r1_xboole_0(k2_xboole_0(X1,sK2),sK2)) )),
% 1.56/0.60    inference(resolution,[],[f727,f55])).
% 1.56/0.60  fof(f55,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f27])).
% 1.56/0.60  fof(f27,plain,(
% 1.56/0.60    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.56/0.60    inference(ennf_transformation,[],[f4])).
% 1.56/0.60  fof(f4,axiom,(
% 1.56/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.56/0.60  fof(f727,plain,(
% 1.56/0.60    ( ! [X1] : (~r1_xboole_0(sK2,k2_xboole_0(X1,sK2))) )),
% 1.56/0.60    inference(resolution,[],[f724,f54])).
% 1.56/0.60  fof(f54,plain,(
% 1.56/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f26])).
% 1.56/0.60  fof(f26,plain,(
% 1.56/0.60    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.56/0.60    inference(ennf_transformation,[],[f7])).
% 1.56/0.60  fof(f7,axiom,(
% 1.56/0.60    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.56/0.60  fof(f724,plain,(
% 1.56/0.60    ~r1_xboole_0(sK2,sK2)),
% 1.56/0.60    inference(subsumption_resolution,[],[f720,f629])).
% 1.56/0.60  fof(f629,plain,(
% 1.56/0.60    ( ! [X0] : (~r1_xboole_0(X0,X0) | ~r1_tarski(X0,sK2)) )),
% 1.56/0.60    inference(superposition,[],[f626,f47])).
% 1.56/0.60  fof(f47,plain,(
% 1.56/0.60    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.56/0.60    inference(cnf_transformation,[],[f23])).
% 1.56/0.60  fof(f23,plain,(
% 1.56/0.60    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.56/0.60    inference(ennf_transformation,[],[f6])).
% 1.56/0.60  fof(f6,axiom,(
% 1.56/0.60    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.56/0.60  fof(f626,plain,(
% 1.56/0.60    ~r1_tarski(k1_xboole_0,sK2)),
% 1.56/0.60    inference(trivial_inequality_removal,[],[f625])).
% 1.56/0.60  fof(f625,plain,(
% 1.56/0.60    sK2 != sK2 | ~r1_tarski(k1_xboole_0,sK2)),
% 1.56/0.60    inference(superposition,[],[f612,f50])).
% 1.56/0.60  fof(f50,plain,(
% 1.56/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f25])).
% 1.56/0.60  fof(f25,plain,(
% 1.56/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.56/0.60    inference(ennf_transformation,[],[f5])).
% 1.56/0.60  fof(f5,axiom,(
% 1.56/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.56/0.60  fof(f612,plain,(
% 1.56/0.60    sK2 != k2_xboole_0(k1_xboole_0,sK2)),
% 1.56/0.60    inference(superposition,[],[f587,f454])).
% 1.56/0.60  fof(f454,plain,(
% 1.56/0.60    k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 1.56/0.60    inference(backward_demodulation,[],[f65,f450])).
% 1.56/0.60  fof(f450,plain,(
% 1.56/0.60    k1_xboole_0 = sK1),
% 1.56/0.60    inference(subsumption_resolution,[],[f448,f182])).
% 1.56/0.60  fof(f182,plain,(
% 1.56/0.60    sK1 = k2_xboole_0(sK1,sK2) | k1_xboole_0 = sK1),
% 1.56/0.60    inference(resolution,[],[f83,f51])).
% 1.56/0.60  fof(f51,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.56/0.60    inference(cnf_transformation,[],[f8])).
% 1.56/0.60  fof(f8,axiom,(
% 1.56/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.56/0.60  fof(f83,plain,(
% 1.56/0.60    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0) )),
% 1.56/0.60    inference(forward_demodulation,[],[f73,f65])).
% 1.56/0.60  fof(f73,plain,(
% 1.56/0.60    ( ! [X0] : (k2_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(sK0,sK0))) )),
% 1.56/0.60    inference(superposition,[],[f65,f68])).
% 1.56/0.60  fof(f68,plain,(
% 1.56/0.60    ( ! [X0,X1] : (k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X1))) )),
% 1.56/0.60    inference(definition_unfolding,[],[f43,f49,f49])).
% 1.56/0.60  fof(f49,plain,(
% 1.56/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f9])).
% 1.56/0.60  fof(f9,axiom,(
% 1.56/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.56/0.60  fof(f43,plain,(
% 1.56/0.60    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.56/0.60    inference(cnf_transformation,[],[f32])).
% 1.56/0.60  fof(f32,plain,(
% 1.56/0.60    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.56/0.60    inference(flattening,[],[f31])).
% 1.56/0.60  fof(f31,plain,(
% 1.56/0.60    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.56/0.60    inference(nnf_transformation,[],[f17])).
% 1.56/0.60  fof(f17,axiom,(
% 1.56/0.60    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.56/0.60  fof(f448,plain,(
% 1.56/0.60    sK1 != k2_xboole_0(sK1,sK2) | k1_xboole_0 = sK1),
% 1.56/0.60    inference(superposition,[],[f345,f65])).
% 1.56/0.60  fof(f345,plain,(
% 1.56/0.60    sK1 != k2_tarski(sK0,sK0) | k1_xboole_0 = sK1),
% 1.56/0.60    inference(trivial_inequality_removal,[],[f297])).
% 1.56/0.60  fof(f297,plain,(
% 1.56/0.60    k1_xboole_0 != k1_xboole_0 | sK1 != k2_tarski(sK0,sK0) | k1_xboole_0 = sK1),
% 1.56/0.60    inference(superposition,[],[f62,f293])).
% 1.56/0.60  fof(f293,plain,(
% 1.56/0.60    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.56/0.60    inference(resolution,[],[f285,f47])).
% 1.56/0.60  fof(f285,plain,(
% 1.56/0.60    r1_xboole_0(sK2,sK2) | k1_xboole_0 = sK1),
% 1.56/0.60    inference(resolution,[],[f260,f54])).
% 1.56/0.60  fof(f260,plain,(
% 1.56/0.60    r1_xboole_0(sK2,k2_xboole_0(sK1,sK2)) | k1_xboole_0 = sK1),
% 1.56/0.60    inference(resolution,[],[f246,f55])).
% 1.56/0.60  fof(f246,plain,(
% 1.56/0.60    r1_xboole_0(k2_xboole_0(sK1,sK2),sK2) | k1_xboole_0 = sK1),
% 1.56/0.60    inference(resolution,[],[f244,f74])).
% 1.56/0.60  fof(f74,plain,(
% 1.56/0.60    ( ! [X0] : (r2_hidden(sK0,X0) | r1_xboole_0(k2_xboole_0(sK1,sK2),X0)) )),
% 1.56/0.60    inference(superposition,[],[f69,f65])).
% 1.56/0.60  fof(f69,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.56/0.60    inference(definition_unfolding,[],[f48,f49])).
% 1.56/0.60  fof(f48,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f24])).
% 1.56/0.60  fof(f24,plain,(
% 1.56/0.60    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.56/0.60    inference(ennf_transformation,[],[f16])).
% 1.56/0.60  fof(f16,axiom,(
% 1.56/0.60    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.56/0.60  fof(f244,plain,(
% 1.56/0.60    ~r2_hidden(sK0,sK2) | k1_xboole_0 = sK1),
% 1.56/0.60    inference(duplicate_literal_removal,[],[f234])).
% 1.56/0.60  fof(f234,plain,(
% 1.56/0.60    ~r2_hidden(sK0,sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.56/0.60    inference(resolution,[],[f194,f206])).
% 1.56/0.60  fof(f206,plain,(
% 1.56/0.60    ~r1_tarski(sK1,sK2) | k1_xboole_0 = sK1),
% 1.56/0.60    inference(subsumption_resolution,[],[f191,f168])).
% 1.56/0.60  fof(f168,plain,(
% 1.56/0.60    sK1 != sK2 | ~r1_tarski(sK1,sK2)),
% 1.56/0.60    inference(trivial_inequality_removal,[],[f167])).
% 1.56/0.60  fof(f167,plain,(
% 1.56/0.60    sK1 != sK2 | sK2 != sK2 | ~r1_tarski(sK1,sK2)),
% 1.56/0.60    inference(superposition,[],[f124,f50])).
% 1.56/0.60  fof(f124,plain,(
% 1.56/0.60    sK1 != k2_xboole_0(sK1,sK2) | sK2 != k2_xboole_0(sK1,sK2)),
% 1.56/0.60    inference(superposition,[],[f64,f65])).
% 1.56/0.60  fof(f64,plain,(
% 1.56/0.60    sK2 != k2_tarski(sK0,sK0) | sK1 != k2_tarski(sK0,sK0)),
% 1.56/0.60    inference(definition_unfolding,[],[f40,f49,f49])).
% 1.56/0.60  fof(f40,plain,(
% 1.56/0.60    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.56/0.60    inference(cnf_transformation,[],[f30])).
% 1.56/0.60  fof(f30,plain,(
% 1.56/0.60    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.56/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f29])).
% 1.56/0.60  fof(f29,plain,(
% 1.56/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.56/0.60    introduced(choice_axiom,[])).
% 1.56/0.60  fof(f22,plain,(
% 1.56/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.56/0.60    inference(ennf_transformation,[],[f21])).
% 1.56/0.60  fof(f21,negated_conjecture,(
% 1.56/0.60    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.56/0.60    inference(negated_conjecture,[],[f20])).
% 1.56/0.60  fof(f20,conjecture,(
% 1.56/0.60    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.56/0.60  fof(f191,plain,(
% 1.56/0.60    sK1 = sK2 | k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2)),
% 1.56/0.60    inference(superposition,[],[f182,f50])).
% 1.56/0.60  fof(f194,plain,(
% 1.56/0.60    ( ! [X0] : (r1_tarski(sK1,X0) | ~r2_hidden(sK0,X0) | k1_xboole_0 = sK1) )),
% 1.56/0.60    inference(superposition,[],[f82,f182])).
% 1.56/0.60  fof(f82,plain,(
% 1.56/0.60    ( ! [X5] : (r1_tarski(k2_xboole_0(sK1,sK2),X5) | ~r2_hidden(sK0,X5)) )),
% 1.56/0.60    inference(duplicate_literal_removal,[],[f81])).
% 1.56/0.60  fof(f81,plain,(
% 1.56/0.60    ( ! [X5] : (r1_tarski(k2_xboole_0(sK1,sK2),X5) | ~r2_hidden(sK0,X5) | ~r2_hidden(sK0,X5)) )),
% 1.56/0.60    inference(superposition,[],[f58,f65])).
% 1.56/0.60  fof(f58,plain,(
% 1.56/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f34])).
% 1.56/0.60  fof(f34,plain,(
% 1.56/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.56/0.60    inference(flattening,[],[f33])).
% 1.56/0.60  fof(f33,plain,(
% 1.56/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.56/0.60    inference(nnf_transformation,[],[f19])).
% 1.56/0.60  fof(f19,axiom,(
% 1.56/0.60    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.56/0.60  fof(f62,plain,(
% 1.56/0.60    k1_xboole_0 != sK2 | sK1 != k2_tarski(sK0,sK0)),
% 1.56/0.60    inference(definition_unfolding,[],[f42,f49])).
% 1.56/0.60  fof(f42,plain,(
% 1.56/0.60    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.56/0.60    inference(cnf_transformation,[],[f30])).
% 1.56/0.60  fof(f65,plain,(
% 1.56/0.60    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0)),
% 1.56/0.60    inference(definition_unfolding,[],[f39,f49])).
% 1.56/0.60  fof(f39,plain,(
% 1.56/0.60    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.56/0.60    inference(cnf_transformation,[],[f30])).
% 1.56/0.60  fof(f587,plain,(
% 1.56/0.60    sK2 != k2_tarski(sK0,sK0)),
% 1.56/0.60    inference(trivial_inequality_removal,[],[f452])).
% 1.56/0.60  fof(f452,plain,(
% 1.56/0.60    k1_xboole_0 != k1_xboole_0 | sK2 != k2_tarski(sK0,sK0)),
% 1.56/0.60    inference(backward_demodulation,[],[f63,f450])).
% 1.56/0.60  fof(f63,plain,(
% 1.56/0.60    k1_xboole_0 != sK1 | sK2 != k2_tarski(sK0,sK0)),
% 1.56/0.60    inference(definition_unfolding,[],[f41,f49])).
% 1.56/0.60  fof(f41,plain,(
% 1.56/0.60    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.56/0.60    inference(cnf_transformation,[],[f30])).
% 1.56/0.60  fof(f720,plain,(
% 1.56/0.60    ~r1_xboole_0(sK2,sK2) | r1_tarski(sK2,sK2)),
% 1.56/0.60    inference(resolution,[],[f634,f61])).
% 1.56/0.60  fof(f61,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f38])).
% 1.56/0.60  fof(f38,plain,(
% 1.56/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.56/0.60  fof(f37,plain,(
% 1.56/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.56/0.60    introduced(choice_axiom,[])).
% 1.56/0.60  fof(f36,plain,(
% 1.56/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.60    inference(rectify,[],[f35])).
% 1.56/0.60  fof(f35,plain,(
% 1.56/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.60    inference(nnf_transformation,[],[f28])).
% 1.56/0.60  fof(f28,plain,(
% 1.56/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.56/0.60    inference(ennf_transformation,[],[f2])).
% 1.56/0.60  fof(f2,axiom,(
% 1.56/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.60  fof(f634,plain,(
% 1.56/0.60    ( ! [X0] : (r2_hidden(sK3(X0,sK2),X0) | ~r1_xboole_0(X0,X0)) )),
% 1.56/0.60    inference(superposition,[],[f627,f47])).
% 1.56/0.60  fof(f627,plain,(
% 1.56/0.60    r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0)),
% 1.56/0.60    inference(resolution,[],[f626,f60])).
% 1.56/0.60  fof(f60,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f38])).
% 1.56/0.60  fof(f853,plain,(
% 1.56/0.60    r1_xboole_0(k2_xboole_0(k1_xboole_0,sK2),sK2)),
% 1.56/0.60    inference(resolution,[],[f846,f455])).
% 1.56/0.60  fof(f455,plain,(
% 1.56/0.60    ( ! [X0] : (r2_hidden(sK0,X0) | r1_xboole_0(k2_xboole_0(k1_xboole_0,sK2),X0)) )),
% 1.56/0.60    inference(backward_demodulation,[],[f74,f450])).
% 1.56/0.60  fof(f846,plain,(
% 1.56/0.60    ~r2_hidden(sK0,sK2)),
% 1.56/0.60    inference(resolution,[],[f845,f459])).
% 1.56/0.60  fof(f459,plain,(
% 1.56/0.60    ( ! [X5] : (r1_tarski(k2_xboole_0(k1_xboole_0,sK2),X5) | ~r2_hidden(sK0,X5)) )),
% 1.56/0.60    inference(backward_demodulation,[],[f82,f450])).
% 1.56/0.60  fof(f845,plain,(
% 1.56/0.60    ~r1_tarski(k2_xboole_0(k1_xboole_0,sK2),sK2)),
% 1.56/0.60    inference(subsumption_resolution,[],[f842,f627])).
% 1.56/0.60  fof(f842,plain,(
% 1.56/0.60    ~r1_tarski(k2_xboole_0(k1_xboole_0,sK2),sK2) | ~r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0)),
% 1.56/0.60    inference(resolution,[],[f636,f461])).
% 1.56/0.60  fof(f461,plain,(
% 1.56/0.60    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(k1_xboole_0,sK2)) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.56/0.60    inference(backward_demodulation,[],[f84,f450])).
% 1.56/0.60  fof(f84,plain,(
% 1.56/0.60    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(sK1,sK2)) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.56/0.60    inference(resolution,[],[f77,f59])).
% 1.56/0.60  fof(f59,plain,(
% 1.56/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f38])).
% 1.56/0.60  fof(f77,plain,(
% 1.56/0.60    r1_tarski(k1_xboole_0,k2_xboole_0(sK1,sK2))),
% 1.56/0.60    inference(superposition,[],[f71,f65])).
% 1.56/0.60  fof(f71,plain,(
% 1.56/0.60    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X1))) )),
% 1.56/0.60    inference(equality_resolution,[],[f67])).
% 1.56/0.60  fof(f67,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_tarski(X1,X1)) | k1_xboole_0 != X0) )),
% 1.56/0.60    inference(definition_unfolding,[],[f44,f49])).
% 1.56/0.60  fof(f44,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 1.56/0.60    inference(cnf_transformation,[],[f32])).
% 1.56/0.60  fof(f636,plain,(
% 1.56/0.60    ( ! [X0] : (~r2_hidden(sK3(k1_xboole_0,sK2),X0) | ~r1_tarski(X0,sK2)) )),
% 1.56/0.60    inference(resolution,[],[f628,f59])).
% 1.56/0.60  fof(f628,plain,(
% 1.56/0.60    ~r2_hidden(sK3(k1_xboole_0,sK2),sK2)),
% 1.56/0.60    inference(resolution,[],[f626,f61])).
% 1.56/0.60  % SZS output end Proof for theBenchmark
% 1.56/0.60  % (20391)------------------------------
% 1.56/0.60  % (20391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.60  % (20391)Termination reason: Refutation
% 1.56/0.60  
% 1.56/0.60  % (20391)Memory used [KB]: 2046
% 1.56/0.60  % (20391)Time elapsed: 0.167 s
% 1.56/0.60  % (20391)------------------------------
% 1.56/0.60  % (20391)------------------------------
% 1.56/0.60  % (20420)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.56/0.60  % (20392)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.56/0.60  % (20409)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.56/0.60  % (20410)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.90/0.61  % (20390)Success in time 0.238 s
%------------------------------------------------------------------------------
