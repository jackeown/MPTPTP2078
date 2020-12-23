%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0326+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 347 expanded)
%              Number of leaves         :    8 ( 103 expanded)
%              Depth                    :   22
%              Number of atoms          :  149 (1285 expanded)
%              Number of equality atoms :   62 ( 340 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(resolution,[],[f218,f23])).

fof(f23,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f218,plain,(
    ! [X0] : ~ v1_xboole_0(X0) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f188,f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f188,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f20,f187])).

fof(f187,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f186,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,o_0_0_xboole_0),k2_zfmisc_1(X1,sK3))
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f90,f93])).

fof(f93,plain,(
    o_0_0_xboole_0 = sK1 ),
    inference(resolution,[],[f72,f23])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sK1 = X0 ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sK1 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f67,f25])).

fof(f67,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f20,f64])).

fof(f64,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f62,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = X0
      | ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) ) ),
    inference(trivial_inequality_removal,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0
      | ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) ) ),
    inference(superposition,[],[f26,f35])).

fof(f35,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k2_zfmisc_1(X2,sK1)
      | ~ r1_tarski(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,sK3)) ) ),
    inference(resolution,[],[f22,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f22,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(sK1,sK3)
    & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) )
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r1_tarski(X1,X3)
            & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X3,X2,X1] :
        ( ~ r1_tarski(X1,X3)
        & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
          | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
   => ( ~ r1_tarski(sK1,sK3)
      & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
        | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f62,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(trivial_inequality_removal,[],[f57])).

fof(f57,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(superposition,[],[f26,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f36,f22])).

fof(f36,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | r1_tarski(sK1,sK3)
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK0) ),
    inference(resolution,[],[f21,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X2)
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) ) ),
    inference(subsumption_resolution,[],[f83,f24])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,sK3)
      | k1_xboole_0 = X0
      | ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) ) ),
    inference(superposition,[],[f22,f55])).

fof(f186,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(k2_zfmisc_1(sK0,o_0_0_xboole_0),k2_zfmisc_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f177,f24])).

fof(f177,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,X3))
      | k1_xboole_0 = sK0
      | r1_tarski(k2_zfmisc_1(sK0,o_0_0_xboole_0),k2_zfmisc_1(sK2,sK3)) ) ),
    inference(superposition,[],[f114,f121])).

fof(f121,plain,
    ( k1_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,sK0)
    | r1_tarski(k2_zfmisc_1(sK0,o_0_0_xboole_0),k2_zfmisc_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f100,f93])).

fof(f100,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,o_0_0_xboole_0),k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f42,f93])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(o_0_0_xboole_0,X0),k2_zfmisc_1(sK3,X1))
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f81,f93])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)) ) ),
    inference(subsumption_resolution,[],[f77,f24])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,sK3)
      | k1_xboole_0 = X0
      | ~ r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)) ) ),
    inference(superposition,[],[f22,f49])).

fof(f49,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_zfmisc_1(sK1,X1),k2_zfmisc_1(sK3,X2)) ) ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1
      | ~ r1_tarski(k2_zfmisc_1(sK1,X1),k2_zfmisc_1(sK3,X2)) ) ),
    inference(superposition,[],[f26,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(sK1,X0)
      | ~ r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)) ) ),
    inference(resolution,[],[f22,f29])).

fof(f20,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
