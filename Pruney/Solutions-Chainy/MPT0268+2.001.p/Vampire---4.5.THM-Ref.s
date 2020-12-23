%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:36 EST 2020

% Result     : Theorem 5.46s
% Output     : Refutation 5.46s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 129 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   18
%              Number of atoms          :  215 ( 465 expanded)
%              Number of equality atoms :   51 ( 105 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6750,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6746,f97])).

fof(f97,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f92,f90])).

fof(f90,plain,
    ( r1_xboole_0(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f54,f48])).

fof(f48,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f54,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f92,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X3,k1_tarski(X2))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f68,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f6746,plain,(
    r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f6587,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f6587,plain,(
    ~ r1_xboole_0(k1_tarski(sK1),sK0) ),
    inference(subsumption_resolution,[],[f6578,f97])).

fof(f6578,plain,
    ( r2_hidden(sK1,sK0)
    | ~ r1_xboole_0(k1_tarski(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f6577])).

fof(f6577,plain,
    ( sK0 != sK0
    | r2_hidden(sK1,sK0)
    | ~ r1_xboole_0(k1_tarski(sK1),sK0) ),
    inference(superposition,[],[f49,f3300])).

fof(f3300,plain,(
    ! [X31,X32] :
      ( k4_xboole_0(X32,X31) = X32
      | ~ r1_xboole_0(X31,X32) ) ),
    inference(superposition,[],[f3042,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f3042,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4 ),
    inference(forward_demodulation,[],[f3002,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f3002,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k1_xboole_0) = k4_xboole_0(X4,k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f59,f2696])).

fof(f2696,plain,(
    ! [X12,X13] : k1_xboole_0 = k3_xboole_0(X13,k4_xboole_0(X12,X13)) ),
    inference(subsumption_resolution,[],[f2688,f371])).

fof(f371,plain,(
    ! [X14,X15,X13] :
      ( k1_xboole_0 = k3_xboole_0(X13,k4_xboole_0(X14,X15))
      | ~ r2_hidden(sK2(k3_xboole_0(X13,k4_xboole_0(X14,X15))),k3_xboole_0(X14,X15)) ) ),
    inference(resolution,[],[f111,f177])).

fof(f177,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k4_xboole_0(X2,X3))
      | ~ r2_hidden(X4,k3_xboole_0(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f172,f88])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f172,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k4_xboole_0(X2,X3))
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,k3_xboole_0(X2,X3)) ) ),
    inference(superposition,[],[f79,f59])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k3_xboole_0(X0,X1)),X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f87,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2688,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK2(k3_xboole_0(X13,k4_xboole_0(X12,X13))),k3_xboole_0(X12,X13))
      | k1_xboole_0 = k3_xboole_0(X13,k4_xboole_0(X12,X13)) ) ),
    inference(superposition,[],[f188,f254])).

fof(f254,plain,(
    ! [X4,X3] : k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(X4,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f253,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f253,plain,(
    ! [X4,X3] : k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(k4_xboole_0(X3,X4),X4) ),
    inference(forward_demodulation,[],[f241,f59])).

fof(f241,plain,(
    ! [X4,X3] : k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X4) ),
    inference(superposition,[],[f71,f59])).

fof(f71,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f188,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k4_xboole_0(X0,X1)),X0)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f164,f52])).

fof(f164,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k4_xboole_0(X2,X3))
      | r2_hidden(X4,X2) ) ),
    inference(subsumption_resolution,[],[f160,f88])).

fof(f160,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k4_xboole_0(X2,X3))
      | r2_hidden(X4,X2)
      | r2_hidden(X4,k3_xboole_0(X2,X3)) ) ),
    inference(superposition,[],[f78,f59])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,
    ( sK0 != k4_xboole_0(sK0,k1_tarski(sK1))
    | r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (15564)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (15557)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (15547)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (15552)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (15551)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (15552)Refutation not found, incomplete strategy% (15552)------------------------------
% 0.20/0.52  % (15552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15552)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (15552)Memory used [KB]: 6140
% 0.20/0.52  % (15552)Time elapsed: 0.116 s
% 0.20/0.52  % (15552)------------------------------
% 0.20/0.52  % (15552)------------------------------
% 0.20/0.52  % (15546)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (15553)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (15542)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (15541)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (15554)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (15563)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (15543)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (15544)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (15568)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (15545)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (15568)Refutation not found, incomplete strategy% (15568)------------------------------
% 0.20/0.53  % (15568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15565)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (15569)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (15566)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (15568)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15568)Memory used [KB]: 6268
% 0.20/0.54  % (15568)Time elapsed: 0.130 s
% 0.20/0.54  % (15568)------------------------------
% 0.20/0.54  % (15568)------------------------------
% 0.20/0.54  % (15550)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (15551)Refutation not found, incomplete strategy% (15551)------------------------------
% 0.20/0.54  % (15551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15551)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15551)Memory used [KB]: 10746
% 0.20/0.54  % (15551)Time elapsed: 0.136 s
% 0.20/0.54  % (15551)------------------------------
% 0.20/0.54  % (15551)------------------------------
% 0.20/0.54  % (15558)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (15559)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (15567)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (15560)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (15571)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (15548)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (15571)Refutation not found, incomplete strategy% (15571)------------------------------
% 0.20/0.54  % (15571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15571)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15571)Memory used [KB]: 1663
% 0.20/0.54  % (15571)Time elapsed: 0.001 s
% 0.20/0.54  % (15571)------------------------------
% 0.20/0.54  % (15571)------------------------------
% 0.20/0.54  % (15549)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (15570)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (15570)Refutation not found, incomplete strategy% (15570)------------------------------
% 0.20/0.55  % (15570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (15570)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (15570)Memory used [KB]: 10746
% 0.20/0.55  % (15570)Time elapsed: 0.149 s
% 0.20/0.55  % (15570)------------------------------
% 0.20/0.55  % (15570)------------------------------
% 0.20/0.55  % (15561)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (15562)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (15556)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (15556)Refutation not found, incomplete strategy% (15556)------------------------------
% 0.20/0.55  % (15556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (15556)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (15556)Memory used [KB]: 1663
% 0.20/0.55  % (15556)Time elapsed: 0.150 s
% 0.20/0.55  % (15556)------------------------------
% 0.20/0.55  % (15556)------------------------------
% 0.20/0.55  % (15558)Refutation not found, incomplete strategy% (15558)------------------------------
% 0.20/0.55  % (15558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (15558)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (15558)Memory used [KB]: 10618
% 0.20/0.55  % (15558)Time elapsed: 0.158 s
% 0.20/0.55  % (15558)------------------------------
% 0.20/0.55  % (15558)------------------------------
% 0.20/0.56  % (15559)Refutation not found, incomplete strategy% (15559)------------------------------
% 0.20/0.56  % (15559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (15559)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (15559)Memory used [KB]: 1663
% 0.20/0.56  % (15559)Time elapsed: 0.157 s
% 0.20/0.56  % (15559)------------------------------
% 0.20/0.56  % (15559)------------------------------
% 2.10/0.67  % (15544)Refutation not found, incomplete strategy% (15544)------------------------------
% 2.10/0.67  % (15544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.67  % (15593)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.10/0.67  % (15594)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.10/0.67  % (15595)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.10/0.67  % (15544)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.67  
% 2.10/0.67  % (15544)Memory used [KB]: 6140
% 2.10/0.67  % (15544)Time elapsed: 0.268 s
% 2.10/0.67  % (15544)------------------------------
% 2.10/0.67  % (15544)------------------------------
% 2.10/0.68  % (15596)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.10/0.69  % (15597)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.10/0.69  % (15598)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.10/0.70  % (15597)Refutation not found, incomplete strategy% (15597)------------------------------
% 2.10/0.70  % (15597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.70  % (15600)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.10/0.70  % (15597)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.70  
% 2.10/0.70  % (15597)Memory used [KB]: 10618
% 2.10/0.70  % (15597)Time elapsed: 0.131 s
% 2.10/0.70  % (15597)------------------------------
% 2.10/0.70  % (15597)------------------------------
% 2.10/0.71  % (15599)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.35/0.81  % (15543)Time limit reached!
% 3.35/0.81  % (15543)------------------------------
% 3.35/0.81  % (15543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.81  % (15606)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.35/0.82  % (15543)Termination reason: Time limit
% 3.35/0.82  
% 3.35/0.82  % (15543)Memory used [KB]: 7419
% 3.35/0.82  % (15543)Time elapsed: 0.408 s
% 3.35/0.82  % (15543)------------------------------
% 3.35/0.82  % (15543)------------------------------
% 3.35/0.83  % (15613)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.35/0.83  % (15566)Time limit reached!
% 3.35/0.83  % (15566)------------------------------
% 3.35/0.83  % (15566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.84  % (15566)Termination reason: Time limit
% 3.35/0.84  
% 3.35/0.84  % (15566)Memory used [KB]: 12409
% 3.35/0.84  % (15566)Time elapsed: 0.429 s
% 3.35/0.84  % (15566)------------------------------
% 3.35/0.84  % (15566)------------------------------
% 3.35/0.86  % (15613)Refutation not found, incomplete strategy% (15613)------------------------------
% 3.35/0.86  % (15613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.86  % (15613)Termination reason: Refutation not found, incomplete strategy
% 3.35/0.86  
% 3.35/0.86  % (15613)Memory used [KB]: 10746
% 3.35/0.86  % (15613)Time elapsed: 0.135 s
% 3.35/0.86  % (15613)------------------------------
% 3.35/0.86  % (15613)------------------------------
% 4.33/0.93  % (15614)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 4.33/0.96  % (15547)Time limit reached!
% 4.33/0.96  % (15547)------------------------------
% 4.33/0.96  % (15547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.33/0.96  % (15547)Termination reason: Time limit
% 4.33/0.96  % (15547)Termination phase: Saturation
% 4.33/0.96  
% 4.33/0.96  % (15547)Memory used [KB]: 15991
% 4.33/0.96  % (15547)Time elapsed: 0.500 s
% 4.33/0.96  % (15547)------------------------------
% 4.33/0.96  % (15547)------------------------------
% 4.33/0.99  % (15615)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 4.33/1.01  % (15548)Time limit reached!
% 4.33/1.01  % (15548)------------------------------
% 4.33/1.01  % (15548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.99/1.02  % (15616)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 4.99/1.04  % (15548)Termination reason: Time limit
% 4.99/1.04  % (15548)Termination phase: Saturation
% 4.99/1.04  
% 4.99/1.04  % (15548)Memory used [KB]: 4861
% 4.99/1.04  % (15548)Time elapsed: 0.600 s
% 4.99/1.04  % (15548)------------------------------
% 4.99/1.04  % (15548)------------------------------
% 5.46/1.10  % (15550)Refutation found. Thanks to Tanya!
% 5.46/1.10  % SZS status Theorem for theBenchmark
% 5.46/1.10  % SZS output start Proof for theBenchmark
% 5.46/1.10  fof(f6750,plain,(
% 5.46/1.10    $false),
% 5.46/1.10    inference(subsumption_resolution,[],[f6746,f97])).
% 5.46/1.10  fof(f97,plain,(
% 5.46/1.10    ~r2_hidden(sK1,sK0)),
% 5.46/1.10    inference(duplicate_literal_removal,[],[f96])).
% 5.46/1.10  fof(f96,plain,(
% 5.46/1.10    ~r2_hidden(sK1,sK0) | ~r2_hidden(sK1,sK0)),
% 5.46/1.10    inference(resolution,[],[f92,f90])).
% 5.46/1.10  fof(f90,plain,(
% 5.46/1.10    r1_xboole_0(sK0,k1_tarski(sK1)) | ~r2_hidden(sK1,sK0)),
% 5.46/1.10    inference(superposition,[],[f54,f48])).
% 5.46/1.10  fof(f48,plain,(
% 5.46/1.10    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~r2_hidden(sK1,sK0)),
% 5.46/1.10    inference(cnf_transformation,[],[f36])).
% 5.46/1.10  fof(f36,plain,(
% 5.46/1.10    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 5.46/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).
% 5.46/1.10  fof(f35,plain,(
% 5.46/1.10    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 5.46/1.10    introduced(choice_axiom,[])).
% 5.46/1.10  fof(f34,plain,(
% 5.46/1.10    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 5.46/1.10    inference(nnf_transformation,[],[f27])).
% 5.46/1.10  fof(f27,plain,(
% 5.46/1.10    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 5.46/1.10    inference(ennf_transformation,[],[f25])).
% 5.46/1.10  fof(f25,negated_conjecture,(
% 5.46/1.10    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 5.46/1.10    inference(negated_conjecture,[],[f24])).
% 5.46/1.10  fof(f24,conjecture,(
% 5.46/1.10    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 5.46/1.10  fof(f54,plain,(
% 5.46/1.10    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 5.46/1.10    inference(cnf_transformation,[],[f12])).
% 5.46/1.10  fof(f12,axiom,(
% 5.46/1.10    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 5.46/1.10  fof(f92,plain,(
% 5.46/1.10    ( ! [X2,X3] : (~r1_xboole_0(X3,k1_tarski(X2)) | ~r2_hidden(X2,X3)) )),
% 5.46/1.10    inference(resolution,[],[f68,f61])).
% 5.46/1.10  fof(f61,plain,(
% 5.46/1.10    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 5.46/1.10    inference(cnf_transformation,[],[f30])).
% 5.46/1.10  fof(f30,plain,(
% 5.46/1.10    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 5.46/1.10    inference(ennf_transformation,[],[f4])).
% 5.46/1.10  fof(f4,axiom,(
% 5.46/1.10    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 5.46/1.10  fof(f68,plain,(
% 5.46/1.10    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 5.46/1.10    inference(cnf_transformation,[],[f32])).
% 5.46/1.10  fof(f32,plain,(
% 5.46/1.10    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 5.46/1.10    inference(ennf_transformation,[],[f21])).
% 5.46/1.10  fof(f21,axiom,(
% 5.46/1.10    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 5.46/1.10  fof(f6746,plain,(
% 5.46/1.10    r2_hidden(sK1,sK0)),
% 5.46/1.10    inference(resolution,[],[f6587,f60])).
% 5.46/1.10  fof(f60,plain,(
% 5.46/1.10    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 5.46/1.10    inference(cnf_transformation,[],[f29])).
% 5.46/1.10  fof(f29,plain,(
% 5.46/1.10    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 5.46/1.10    inference(ennf_transformation,[],[f22])).
% 5.46/1.10  fof(f22,axiom,(
% 5.46/1.10    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 5.46/1.10  fof(f6587,plain,(
% 5.46/1.10    ~r1_xboole_0(k1_tarski(sK1),sK0)),
% 5.46/1.10    inference(subsumption_resolution,[],[f6578,f97])).
% 5.46/1.10  fof(f6578,plain,(
% 5.46/1.10    r2_hidden(sK1,sK0) | ~r1_xboole_0(k1_tarski(sK1),sK0)),
% 5.46/1.10    inference(trivial_inequality_removal,[],[f6577])).
% 5.46/1.10  fof(f6577,plain,(
% 5.46/1.10    sK0 != sK0 | r2_hidden(sK1,sK0) | ~r1_xboole_0(k1_tarski(sK1),sK0)),
% 5.46/1.10    inference(superposition,[],[f49,f3300])).
% 5.46/1.10  fof(f3300,plain,(
% 5.46/1.10    ( ! [X31,X32] : (k4_xboole_0(X32,X31) = X32 | ~r1_xboole_0(X31,X32)) )),
% 5.46/1.10    inference(superposition,[],[f3042,f62])).
% 5.46/1.10  fof(f62,plain,(
% 5.46/1.10    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 5.46/1.10    inference(cnf_transformation,[],[f31])).
% 5.46/1.10  fof(f31,plain,(
% 5.46/1.10    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 5.46/1.10    inference(ennf_transformation,[],[f13])).
% 5.46/1.10  fof(f13,axiom,(
% 5.46/1.10    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 5.46/1.10  fof(f3042,plain,(
% 5.46/1.10    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4) )),
% 5.46/1.10    inference(forward_demodulation,[],[f3002,f50])).
% 5.46/1.10  fof(f50,plain,(
% 5.46/1.10    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.46/1.10    inference(cnf_transformation,[],[f11])).
% 5.46/1.10  fof(f11,axiom,(
% 5.46/1.10    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 5.46/1.10  fof(f3002,plain,(
% 5.46/1.10    ( ! [X4,X5] : (k5_xboole_0(X4,k1_xboole_0) = k4_xboole_0(X4,k4_xboole_0(X5,X4))) )),
% 5.46/1.10    inference(superposition,[],[f59,f2696])).
% 5.46/1.10  fof(f2696,plain,(
% 5.46/1.10    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(X13,k4_xboole_0(X12,X13))) )),
% 5.46/1.10    inference(subsumption_resolution,[],[f2688,f371])).
% 5.46/1.10  fof(f371,plain,(
% 5.46/1.10    ( ! [X14,X15,X13] : (k1_xboole_0 = k3_xboole_0(X13,k4_xboole_0(X14,X15)) | ~r2_hidden(sK2(k3_xboole_0(X13,k4_xboole_0(X14,X15))),k3_xboole_0(X14,X15))) )),
% 5.46/1.10    inference(resolution,[],[f111,f177])).
% 5.46/1.10  fof(f177,plain,(
% 5.46/1.10    ( ! [X4,X2,X3] : (~r2_hidden(X4,k4_xboole_0(X2,X3)) | ~r2_hidden(X4,k3_xboole_0(X2,X3))) )),
% 5.46/1.10    inference(subsumption_resolution,[],[f172,f88])).
% 5.46/1.10  fof(f88,plain,(
% 5.46/1.10    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 5.46/1.10    inference(equality_resolution,[],[f72])).
% 5.46/1.10  fof(f72,plain,(
% 5.46/1.10    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 5.46/1.10    inference(cnf_transformation,[],[f46])).
% 5.46/1.10  fof(f46,plain,(
% 5.46/1.10    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 5.46/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 5.46/1.10  fof(f45,plain,(
% 5.46/1.10    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 5.46/1.10    introduced(choice_axiom,[])).
% 5.46/1.10  fof(f44,plain,(
% 5.46/1.10    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 5.46/1.10    inference(rectify,[],[f43])).
% 5.46/1.10  fof(f43,plain,(
% 5.46/1.10    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 5.46/1.10    inference(flattening,[],[f42])).
% 5.46/1.10  fof(f42,plain,(
% 5.46/1.10    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 5.46/1.10    inference(nnf_transformation,[],[f2])).
% 5.46/1.10  fof(f2,axiom,(
% 5.46/1.10    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 5.46/1.10  fof(f172,plain,(
% 5.46/1.10    ( ! [X4,X2,X3] : (~r2_hidden(X4,k4_xboole_0(X2,X3)) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,k3_xboole_0(X2,X3))) )),
% 5.46/1.10    inference(superposition,[],[f79,f59])).
% 5.46/1.10  fof(f79,plain,(
% 5.46/1.10    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 5.46/1.10    inference(cnf_transformation,[],[f47])).
% 5.46/1.10  fof(f47,plain,(
% 5.46/1.10    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 5.46/1.10    inference(nnf_transformation,[],[f33])).
% 5.46/1.10  fof(f33,plain,(
% 5.46/1.10    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 5.46/1.10    inference(ennf_transformation,[],[f5])).
% 5.46/1.10  fof(f5,axiom,(
% 5.46/1.10    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 5.46/1.10  fof(f111,plain,(
% 5.46/1.10    ( ! [X0,X1] : (r2_hidden(sK2(k3_xboole_0(X0,X1)),X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 5.46/1.10    inference(resolution,[],[f87,f52])).
% 5.46/1.10  fof(f52,plain,(
% 5.46/1.10    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 5.46/1.10    inference(cnf_transformation,[],[f38])).
% 5.46/1.10  fof(f38,plain,(
% 5.46/1.10    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 5.46/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f37])).
% 5.46/1.10  fof(f37,plain,(
% 5.46/1.10    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 5.46/1.10    introduced(choice_axiom,[])).
% 5.46/1.10  fof(f28,plain,(
% 5.46/1.10    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 5.46/1.10    inference(ennf_transformation,[],[f6])).
% 5.46/1.10  fof(f6,axiom,(
% 5.46/1.10    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 5.46/1.10  fof(f87,plain,(
% 5.46/1.10    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 5.46/1.10    inference(equality_resolution,[],[f73])).
% 5.46/1.10  fof(f73,plain,(
% 5.46/1.10    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 5.46/1.10    inference(cnf_transformation,[],[f46])).
% 5.46/1.10  fof(f2688,plain,(
% 5.46/1.10    ( ! [X12,X13] : (r2_hidden(sK2(k3_xboole_0(X13,k4_xboole_0(X12,X13))),k3_xboole_0(X12,X13)) | k1_xboole_0 = k3_xboole_0(X13,k4_xboole_0(X12,X13))) )),
% 5.46/1.10    inference(superposition,[],[f188,f254])).
% 5.46/1.10  fof(f254,plain,(
% 5.46/1.10    ( ! [X4,X3] : (k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(X4,k4_xboole_0(X3,X4))) )),
% 5.46/1.10    inference(forward_demodulation,[],[f253,f56])).
% 5.46/1.10  fof(f56,plain,(
% 5.46/1.10    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.46/1.10    inference(cnf_transformation,[],[f1])).
% 5.46/1.10  fof(f1,axiom,(
% 5.46/1.10    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.46/1.10  fof(f253,plain,(
% 5.46/1.10    ( ! [X4,X3] : (k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(k4_xboole_0(X3,X4),X4)) )),
% 5.46/1.10    inference(forward_demodulation,[],[f241,f59])).
% 5.46/1.10  fof(f241,plain,(
% 5.46/1.10    ( ! [X4,X3] : (k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X4)) )),
% 5.46/1.10    inference(superposition,[],[f71,f59])).
% 5.46/1.10  fof(f71,plain,(
% 5.46/1.10    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 5.46/1.10    inference(cnf_transformation,[],[f10])).
% 5.46/1.10  fof(f10,axiom,(
% 5.46/1.10    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 5.46/1.10  fof(f188,plain,(
% 5.46/1.10    ( ! [X0,X1] : (r2_hidden(sK2(k4_xboole_0(X0,X1)),X0) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 5.46/1.10    inference(resolution,[],[f164,f52])).
% 5.46/1.10  fof(f164,plain,(
% 5.46/1.10    ( ! [X4,X2,X3] : (~r2_hidden(X4,k4_xboole_0(X2,X3)) | r2_hidden(X4,X2)) )),
% 5.46/1.10    inference(subsumption_resolution,[],[f160,f88])).
% 5.46/1.10  fof(f160,plain,(
% 5.46/1.10    ( ! [X4,X2,X3] : (~r2_hidden(X4,k4_xboole_0(X2,X3)) | r2_hidden(X4,X2) | r2_hidden(X4,k3_xboole_0(X2,X3))) )),
% 5.46/1.10    inference(superposition,[],[f78,f59])).
% 5.46/1.10  fof(f78,plain,(
% 5.46/1.10    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 5.46/1.10    inference(cnf_transformation,[],[f47])).
% 5.46/1.10  fof(f59,plain,(
% 5.46/1.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.46/1.10    inference(cnf_transformation,[],[f9])).
% 5.46/1.10  fof(f9,axiom,(
% 5.46/1.10    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.46/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.46/1.10  fof(f49,plain,(
% 5.46/1.10    sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) | r2_hidden(sK1,sK0)),
% 5.46/1.10    inference(cnf_transformation,[],[f36])).
% 5.46/1.10  % SZS output end Proof for theBenchmark
% 5.46/1.10  % (15550)------------------------------
% 5.46/1.10  % (15550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.46/1.10  % (15550)Termination reason: Refutation
% 5.46/1.10  
% 5.46/1.10  % (15550)Memory used [KB]: 6396
% 5.46/1.10  % (15550)Time elapsed: 0.694 s
% 5.46/1.10  % (15550)------------------------------
% 5.46/1.10  % (15550)------------------------------
% 5.46/1.10  % (15537)Success in time 0.732 s
%------------------------------------------------------------------------------
