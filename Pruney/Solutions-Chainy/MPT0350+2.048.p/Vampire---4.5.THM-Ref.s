%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:56 EST 2020

% Result     : Theorem 6.90s
% Output     : Refutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :  226 (10013 expanded)
%              Number of leaves         :   28 (2834 expanded)
%              Depth                    :   45
%              Number of atoms          :  440 (28159 expanded)
%              Number of equality atoms :  199 (8361 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9077,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9076,f134])).

fof(f134,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f103,f133])).

fof(f133,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f105,f122])).

fof(f122,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f114,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f114,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f111,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f111,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f110,f99])).

fof(f99,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f110,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f106,f47])).

fof(f47,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f106,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f45,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f105,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f45,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f103,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f46,f48])).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f46,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f9076,plain,(
    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f8013,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f8013,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f7101,f7734])).

fof(f7734,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f7673,f50])).

fof(f7673,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f7036,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f7036,plain,(
    ! [X0] : k5_xboole_0(sK1,sK1) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(duplicate_literal_removal,[],[f6992])).

fof(f6992,plain,(
    ! [X0] :
      ( k5_xboole_0(sK1,sK1) = k5_xboole_0(X0,k3_xboole_0(X0,X0))
      | k5_xboole_0(sK1,sK1) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ) ),
    inference(resolution,[],[f2672,f2671])).

fof(f2671,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,k5_xboole_0(X3,k3_xboole_0(X3,X4))),X3)
      | k5_xboole_0(sK1,sK1) = k5_xboole_0(X3,k3_xboole_0(X3,X4)) ) ),
    inference(backward_demodulation,[],[f1226,f2630])).

fof(f2630,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1141,f2462])).

fof(f2462,plain,(
    sK1 = k3_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f2460,f62])).

fof(f2460,plain,(
    r1_tarski(sK1,sK1) ),
    inference(forward_demodulation,[],[f2459,f122])).

fof(f2459,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f2455,f52])).

fof(f2455,plain,(
    r1_tarski(k3_xboole_0(sK1,sK0),sK1) ),
    inference(superposition,[],[f2424,f50])).

fof(f2424,plain,(
    ! [X2] : r1_tarski(k3_xboole_0(sK1,k5_xboole_0(sK0,X2)),sK1) ),
    inference(superposition,[],[f88,f1141])).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1141,plain,(
    ! [X0] : k3_xboole_0(sK1,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f152,f52])).

fof(f152,plain,(
    ! [X0] : k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f146,f52])).

fof(f146,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f70,f122])).

fof(f70,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f1226,plain,(
    ! [X4,X3] :
      ( k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(X3,k3_xboole_0(X3,X4))
      | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,k5_xboole_0(X3,k3_xboole_0(X3,X4))),X3) ) ),
    inference(backward_demodulation,[],[f619,f1196])).

fof(f1196,plain,(
    k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f424,f1154])).

fof(f1154,plain,(
    ! [X2] : ~ r2_hidden(X2,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1147,f1146])).

fof(f1146,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
      | r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f102,f152])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f72,f56])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1147,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f101,f152])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f73,f56])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f424,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1)
      | k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = X1 ) ),
    inference(backward_demodulation,[],[f326,f415])).

fof(f415,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f142,f140])).

fof(f140,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f121,f133])).

fof(f121,plain,(
    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK0) ),
    inference(resolution,[],[f118,f62])).

fof(f118,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK0) ),
    inference(superposition,[],[f88,f105])).

fof(f142,plain,(
    ! [X0] : k5_xboole_0(sK1,k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f126,f52])).

fof(f126,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(sK1,X0),sK0) = k5_xboole_0(sK1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f70,f114])).

fof(f326,plain,(
    ! [X1] :
      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) = X1
      | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,(
    ! [X1] :
      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) = X1
      | k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) = X1
      | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1) ) ),
    inference(forward_demodulation,[],[f324,f142])).

fof(f324,plain,(
    ! [X1] :
      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),sK0))) = X1
      | k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) = X1
      | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1) ) ),
    inference(forward_demodulation,[],[f323,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f323,plain,(
    ! [X1] :
      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) = X1
      | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1)
      | k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)) = X1 ) ),
    inference(forward_demodulation,[],[f322,f142])).

fof(f322,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1)
      | k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),sK0))) = X1
      | k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f308])).

fof(f308,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1)
      | k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),sK0))) = X1
      | k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)) = X1
      | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1) ) ),
    inference(resolution,[],[f174,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f76,f56])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f174,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(k5_xboole_0(sK0,sK1),X2,X3),sK0)
      | r2_hidden(sK3(k5_xboole_0(sK0,sK1),X2,X3),X3)
      | k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),X2))) = X3 ) ),
    inference(forward_demodulation,[],[f173,f69])).

fof(f173,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(k5_xboole_0(sK0,sK1),X2,X3),sK0)
      | r2_hidden(sK3(k5_xboole_0(sK0,sK1),X2,X3),X3)
      | k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),X2)) = X3 ) ),
    inference(resolution,[],[f135,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f75,f56])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_xboole_0(sK0,sK1))
      | r2_hidden(X0,sK0) ) ),
    inference(backward_demodulation,[],[f115,f133])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_subset_1(sK0,sK1))
      | r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f102,f105])).

fof(f619,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
      | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,k5_xboole_0(X3,k3_xboole_0(X3,X4))),X3) ) ),
    inference(resolution,[],[f424,f102])).

fof(f2672,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,k5_xboole_0(X5,k3_xboole_0(X5,X6))),X6)
      | k5_xboole_0(sK1,sK1) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ) ),
    inference(backward_demodulation,[],[f1227,f2630])).

fof(f1227,plain,(
    ! [X6,X5] :
      ( k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(X5,k3_xboole_0(X5,X6))
      | ~ r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,k5_xboole_0(X5,k3_xboole_0(X5,X6))),X6) ) ),
    inference(backward_demodulation,[],[f620,f1196])).

fof(f620,plain,(
    ! [X6,X5] :
      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k5_xboole_0(X5,k3_xboole_0(X5,X6))
      | ~ r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,k5_xboole_0(X5,k3_xboole_0(X5,X6))),X6) ) ),
    inference(resolution,[],[f424,f101])).

fof(f7101,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f7100,f4989])).

fof(f4989,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(backward_demodulation,[],[f4300,f4988])).

fof(f4988,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f4987,f4297])).

fof(f4297,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f515,f4265])).

fof(f4265,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f517,f416])).

fof(f416,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f142,f114])).

fof(f517,plain,(
    ! [X1] : k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X1))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,X1))) ),
    inference(forward_demodulation,[],[f502,f142])).

fof(f502,plain,(
    ! [X1] : k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X1))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(X1,sK0))) ),
    inference(superposition,[],[f217,f69])).

fof(f217,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f216,f69])).

fof(f216,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),X0)) ),
    inference(forward_demodulation,[],[f209,f52])).

fof(f209,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(k5_xboole_0(sK0,sK1),X0),sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f70,f140])).

fof(f515,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f501,f53])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f501,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f217,f114])).

fof(f4987,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4986,f53])).

fof(f4986,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f4985,f3442])).

fof(f3442,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(X0,k4_subset_1(sK0,sK1,sK1))) ),
    inference(superposition,[],[f3337,f53])).

fof(f3337,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0)) ),
    inference(backward_demodulation,[],[f2618,f3336])).

fof(f3336,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f3330,f69])).

fof(f3330,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(sK1,sK1),X0) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f69,f3303])).

fof(f3303,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1) ),
    inference(forward_demodulation,[],[f3291,f3301])).

fof(f3301,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f3300,f3157])).

fof(f3157,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(sK1,k4_subset_1(sK0,sK1,sK1)) ),
    inference(resolution,[],[f3083,f2664])).

fof(f2664,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1)
      | k5_xboole_0(sK1,sK1) = X1 ) ),
    inference(backward_demodulation,[],[f1212,f2630])).

fof(f1212,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1)
      | k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = X1 ) ),
    inference(backward_demodulation,[],[f424,f1196])).

fof(f3083,plain,(
    ! [X3] : ~ r2_hidden(X3,k5_xboole_0(sK1,k4_subset_1(sK0,sK1,sK1))) ),
    inference(global_subsumption,[],[f2496,f2653])).

fof(f2653,plain,(
    ! [X2] : ~ r2_hidden(X2,k5_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f1154,f2630])).

fof(f2496,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_xboole_0(sK1,k4_subset_1(sK0,sK1,sK1)))
      | r2_hidden(X4,k5_xboole_0(sK1,sK1)) ) ),
    inference(backward_demodulation,[],[f306,f2463])).

fof(f2463,plain,(
    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f159,f2462])).

fof(f159,plain,(
    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(k3_xboole_0(sK1,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(resolution,[],[f109,f45])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k5_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(X0,sK1)) ) ),
    inference(forward_demodulation,[],[f108,f53])).

fof(f108,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,X0,sK1) = k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(X0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(forward_demodulation,[],[f104,f89])).

fof(f89,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f78,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f79,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f104,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,X0,sK1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f45,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f71,f87])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f306,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))))
      | r2_hidden(X4,k5_xboole_0(sK1,sK1)) ) ),
    inference(forward_demodulation,[],[f299,f69])).

fof(f299,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,sK1)))
      | r2_hidden(X4,k5_xboole_0(sK1,sK1)) ) ),
    inference(superposition,[],[f102,f155])).

fof(f155,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1) ),
    inference(resolution,[],[f128,f62])).

fof(f128,plain,(
    r1_tarski(k5_xboole_0(sK1,sK1),sK1) ),
    inference(superposition,[],[f88,f114])).

fof(f3300,plain,(
    k5_xboole_0(sK1,k4_subset_1(sK0,sK1,sK1)) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f3290,f53])).

fof(f3290,plain,(
    k5_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK1,sK1)) ),
    inference(superposition,[],[f3262,f2465])).

fof(f2465,plain,(
    ! [X0] : k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(X0,sK1))) ),
    inference(backward_demodulation,[],[f233,f2462])).

fof(f233,plain,(
    ! [X0] : k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) = k5_xboole_0(k3_xboole_0(sK1,sK1),k5_xboole_0(sK1,k5_xboole_0(X0,sK1))) ),
    inference(superposition,[],[f201,f53])).

fof(f201,plain,(
    ! [X0] : k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) = k5_xboole_0(k3_xboole_0(sK1,sK1),k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f200,f69])).

fof(f200,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(sK1,sK1),k5_xboole_0(k5_xboole_0(sK1,sK1),X0)) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) ),
    inference(superposition,[],[f69,f159])).

fof(f3262,plain,(
    ! [X5] : k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X5) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X5))) ),
    inference(backward_demodulation,[],[f2613,f3261])).

fof(f3261,plain,(
    ! [X0] : k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f3240,f69])).

fof(f3240,plain,(
    ! [X0] : k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(k5_xboole_0(sK1,sK1),X0)) ),
    inference(superposition,[],[f69,f3198])).

fof(f3198,plain,(
    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f3177,f2463])).

fof(f3177,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f2612,f3157])).

fof(f2612,plain,(
    k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_subset_1(sK0,sK1,sK1))) ),
    inference(superposition,[],[f2464,f2463])).

fof(f2464,plain,(
    ! [X0] : k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) ),
    inference(backward_demodulation,[],[f201,f2462])).

fof(f2613,plain,(
    ! [X5] : k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,k5_xboole_0(sK1,X5))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X5))) ),
    inference(superposition,[],[f2464,f2464])).

fof(f3291,plain,(
    k5_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK1,sK1)) ),
    inference(superposition,[],[f2465,f3262])).

fof(f2618,plain,(
    ! [X0] : k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0)) ),
    inference(superposition,[],[f2464,f2464])).

fof(f4985,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK1,k5_xboole_0(sK0,k4_subset_1(sK0,sK1,sK1))) ),
    inference(forward_demodulation,[],[f4981,f4308])).

fof(f4308,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))) = k5_xboole_0(sK0,k4_subset_1(sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f3619,f4297])).

fof(f3619,plain,(
    k5_xboole_0(sK0,k4_subset_1(sK0,sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3594,f3618])).

fof(f3618,plain,(
    k5_xboole_0(sK0,k4_subset_1(sK0,sK1,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) ),
    inference(forward_demodulation,[],[f3617,f53])).

fof(f3617,plain,(
    k5_xboole_0(k4_subset_1(sK0,sK1,sK1),sK0) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) ),
    inference(forward_demodulation,[],[f3616,f2465])).

fof(f3616,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) ),
    inference(forward_demodulation,[],[f3615,f53])).

fof(f3615,plain,(
    k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) ),
    inference(forward_demodulation,[],[f3593,f53])).

fof(f3593,plain,(
    k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),sK1)) ),
    inference(superposition,[],[f434,f515])).

fof(f434,plain,(
    ! [X0] : k3_xboole_0(sK0,k5_xboole_0(X0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,X0),sK1) ),
    inference(superposition,[],[f143,f52])).

fof(f143,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,sK0),sK1) = k3_xboole_0(sK0,k5_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f127,f52])).

fof(f127,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(X1,sK1),sK0) = k5_xboole_0(k3_xboole_0(X1,sK0),sK1) ),
    inference(superposition,[],[f70,f114])).

fof(f3594,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) ),
    inference(superposition,[],[f413,f515])).

fof(f413,plain,(
    ! [X0] : k3_xboole_0(sK0,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f142,f52])).

fof(f4981,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) ),
    inference(superposition,[],[f4300,f69])).

fof(f4300,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(backward_demodulation,[],[f2650,f4297])).

fof(f2650,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f166,f2630])).

fof(f166,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f165,f52])).

fof(f165,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f160,f53])).

fof(f160,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)) ),
    inference(resolution,[],[f158,f109])).

fof(f158,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f157,f47])).

fof(f157,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f139,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f139,plain,(
    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f120,f133])).

fof(f120,plain,(
    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f118,f98])).

fof(f98,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7100,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f7099,f2630])).

fof(f7099,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f7090,f4297])).

fof(f7090,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f168,f45])).

fof(f168,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,sK1)),k5_xboole_0(X0,k5_xboole_0(sK0,sK1))) ) ),
    inference(forward_demodulation,[],[f167,f53])).

fof(f167,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK0,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(forward_demodulation,[],[f161,f89])).

fof(f161,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f158,f91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:58:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (13191)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (13183)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (13182)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (13179)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (13180)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (13178)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (13201)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (13181)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (13201)Refutation not found, incomplete strategy% (13201)------------------------------
% 0.22/0.52  % (13201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13200)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (13188)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (13190)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (13201)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13201)Memory used [KB]: 10746
% 0.22/0.54  % (13201)Time elapsed: 0.111 s
% 0.22/0.54  % (13201)------------------------------
% 0.22/0.54  % (13201)------------------------------
% 0.22/0.54  % (13204)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (13198)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (13189)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (13208)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (13185)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (13207)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (13206)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (13197)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (13196)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (13188)Refutation not found, incomplete strategy% (13188)------------------------------
% 0.22/0.55  % (13188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13188)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (13188)Memory used [KB]: 10618
% 0.22/0.55  % (13188)Time elapsed: 0.137 s
% 0.22/0.55  % (13188)------------------------------
% 0.22/0.55  % (13188)------------------------------
% 0.22/0.55  % (13203)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (13199)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (13205)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (13187)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (13194)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (13193)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (13186)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (13189)Refutation not found, incomplete strategy% (13189)------------------------------
% 0.22/0.56  % (13189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (13189)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (13189)Memory used [KB]: 10618
% 0.22/0.56  % (13189)Time elapsed: 0.152 s
% 0.22/0.56  % (13189)------------------------------
% 0.22/0.56  % (13189)------------------------------
% 0.22/0.57  % (13196)Refutation not found, incomplete strategy% (13196)------------------------------
% 0.22/0.57  % (13196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (13196)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (13196)Memory used [KB]: 10618
% 0.22/0.57  % (13196)Time elapsed: 0.157 s
% 0.22/0.57  % (13196)------------------------------
% 0.22/0.57  % (13196)------------------------------
% 0.22/0.57  % (13184)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.48/0.58  % (13192)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.48/0.58  % (13202)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 2.49/0.73  % (13215)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.49/0.74  % (13231)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.77/0.75  % (13221)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.77/0.82  % (13234)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.77/0.82  % (13183)Time limit reached!
% 2.77/0.82  % (13183)------------------------------
% 2.77/0.82  % (13183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.77/0.82  % (13183)Termination reason: Time limit
% 2.77/0.82  % (13183)Termination phase: Saturation
% 2.77/0.82  
% 2.77/0.82  % (13183)Memory used [KB]: 8699
% 2.77/0.82  % (13183)Time elapsed: 0.400 s
% 2.77/0.82  % (13183)------------------------------
% 2.77/0.82  % (13183)------------------------------
% 3.81/0.91  % (13190)Time limit reached!
% 3.81/0.91  % (13190)------------------------------
% 3.81/0.91  % (13190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.91  % (13190)Termination reason: Time limit
% 3.81/0.91  
% 3.81/0.91  % (13190)Memory used [KB]: 8571
% 3.81/0.91  % (13190)Time elapsed: 0.504 s
% 3.81/0.91  % (13190)------------------------------
% 3.81/0.91  % (13190)------------------------------
% 3.81/0.92  % (13178)Time limit reached!
% 3.81/0.92  % (13178)------------------------------
% 3.81/0.92  % (13178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.92  % (13178)Termination reason: Time limit
% 3.81/0.92  
% 3.81/0.92  % (13178)Memory used [KB]: 4349
% 3.81/0.92  % (13178)Time elapsed: 0.506 s
% 3.81/0.92  % (13178)------------------------------
% 3.81/0.92  % (13178)------------------------------
% 4.20/0.96  % (13179)Time limit reached!
% 4.20/0.96  % (13179)------------------------------
% 4.20/0.96  % (13179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.20/0.98  % (13179)Termination reason: Time limit
% 4.20/0.98  % (13179)Termination phase: Saturation
% 4.20/0.98  
% 4.20/0.98  % (13179)Memory used [KB]: 10106
% 4.20/0.98  % (13179)Time elapsed: 0.500 s
% 4.20/0.98  % (13179)------------------------------
% 4.20/0.98  % (13179)------------------------------
% 4.20/0.99  % (13240)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.50/1.01  % (13194)Time limit reached!
% 4.50/1.01  % (13194)------------------------------
% 4.50/1.01  % (13194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.01  % (13194)Termination reason: Time limit
% 4.50/1.01  % (13194)Termination phase: Saturation
% 4.50/1.01  
% 4.50/1.01  % (13194)Memory used [KB]: 14583
% 4.50/1.01  % (13194)Time elapsed: 0.600 s
% 4.50/1.01  % (13194)------------------------------
% 4.50/1.01  % (13194)------------------------------
% 4.50/1.02  % (13185)Time limit reached!
% 4.50/1.02  % (13185)------------------------------
% 4.50/1.02  % (13185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.02  % (13185)Termination reason: Time limit
% 4.50/1.02  % (13185)Termination phase: Saturation
% 4.50/1.02  
% 4.50/1.02  % (13185)Memory used [KB]: 9850
% 4.50/1.02  % (13185)Time elapsed: 0.600 s
% 4.50/1.02  % (13185)------------------------------
% 4.50/1.02  % (13185)------------------------------
% 4.50/1.05  % (13234)Time limit reached!
% 4.50/1.05  % (13234)------------------------------
% 4.50/1.05  % (13234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.05  % (13234)Termination reason: Time limit
% 4.50/1.05  
% 4.50/1.05  % (13234)Memory used [KB]: 6268
% 4.50/1.05  % (13234)Time elapsed: 0.418 s
% 4.50/1.05  % (13234)------------------------------
% 4.50/1.05  % (13234)------------------------------
% 4.50/1.07  % (13241)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.47/1.07  % (13207)Time limit reached!
% 5.47/1.07  % (13207)------------------------------
% 5.47/1.07  % (13207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.47/1.08  % (13242)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.47/1.09  % (13207)Termination reason: Time limit
% 5.47/1.09  % (13207)Termination phase: Saturation
% 5.47/1.09  
% 5.47/1.09  % (13207)Memory used [KB]: 9338
% 5.47/1.09  % (13207)Time elapsed: 0.660 s
% 5.47/1.09  % (13207)------------------------------
% 5.47/1.09  % (13207)------------------------------
% 5.47/1.13  % (13244)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.47/1.15  % (13245)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.26/1.17  % (13246)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.26/1.17  % (13247)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.26/1.20  % (13252)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.69/1.23  % (13200)Time limit reached!
% 6.69/1.23  % (13200)------------------------------
% 6.69/1.23  % (13200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.69/1.23  % (13200)Termination reason: Time limit
% 6.69/1.23  
% 6.69/1.23  % (13200)Memory used [KB]: 6908
% 6.69/1.23  % (13200)Time elapsed: 0.813 s
% 6.69/1.23  % (13200)------------------------------
% 6.69/1.23  % (13200)------------------------------
% 6.90/1.30  % (13240)Time limit reached!
% 6.90/1.30  % (13240)------------------------------
% 6.90/1.30  % (13240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.90/1.30  % (13240)Termination reason: Time limit
% 6.90/1.30  % (13240)Termination phase: Saturation
% 6.90/1.30  
% 6.90/1.30  % (13240)Memory used [KB]: 14711
% 6.90/1.30  % (13240)Time elapsed: 0.400 s
% 6.90/1.30  % (13240)------------------------------
% 6.90/1.30  % (13240)------------------------------
% 6.90/1.32  % (13186)Refutation found. Thanks to Tanya!
% 6.90/1.32  % SZS status Theorem for theBenchmark
% 7.43/1.33  % SZS output start Proof for theBenchmark
% 7.43/1.33  fof(f9077,plain,(
% 7.43/1.33    $false),
% 7.43/1.33    inference(subsumption_resolution,[],[f9076,f134])).
% 7.43/1.33  fof(f134,plain,(
% 7.43/1.33    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 7.43/1.33    inference(backward_demodulation,[],[f103,f133])).
% 7.43/1.33  fof(f133,plain,(
% 7.43/1.33    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 7.43/1.33    inference(backward_demodulation,[],[f105,f122])).
% 7.43/1.33  fof(f122,plain,(
% 7.43/1.33    sK1 = k3_xboole_0(sK0,sK1)),
% 7.43/1.33    inference(superposition,[],[f114,f52])).
% 7.43/1.33  fof(f52,plain,(
% 7.43/1.33    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f1])).
% 7.43/1.33  fof(f1,axiom,(
% 7.43/1.33    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 7.43/1.33  fof(f114,plain,(
% 7.43/1.33    sK1 = k3_xboole_0(sK1,sK0)),
% 7.43/1.33    inference(resolution,[],[f111,f62])).
% 7.43/1.33  fof(f62,plain,(
% 7.43/1.33    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 7.43/1.33    inference(cnf_transformation,[],[f29])).
% 7.43/1.33  fof(f29,plain,(
% 7.43/1.33    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.43/1.33    inference(ennf_transformation,[],[f6])).
% 7.43/1.33  fof(f6,axiom,(
% 7.43/1.33    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 7.43/1.33  fof(f111,plain,(
% 7.43/1.33    r1_tarski(sK1,sK0)),
% 7.43/1.33    inference(resolution,[],[f110,f99])).
% 7.43/1.33  fof(f99,plain,(
% 7.43/1.33    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 7.43/1.33    inference(equality_resolution,[],[f64])).
% 7.43/1.33  fof(f64,plain,(
% 7.43/1.33    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.43/1.33    inference(cnf_transformation,[],[f39])).
% 7.43/1.33  fof(f39,plain,(
% 7.43/1.33    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.43/1.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 7.43/1.33  fof(f38,plain,(
% 7.43/1.33    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 7.43/1.33    introduced(choice_axiom,[])).
% 7.43/1.33  fof(f37,plain,(
% 7.43/1.33    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.43/1.33    inference(rectify,[],[f36])).
% 7.43/1.33  fof(f36,plain,(
% 7.43/1.33    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.43/1.33    inference(nnf_transformation,[],[f18])).
% 7.43/1.33  fof(f18,axiom,(
% 7.43/1.33    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 7.43/1.33  fof(f110,plain,(
% 7.43/1.33    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 7.43/1.33    inference(subsumption_resolution,[],[f106,f47])).
% 7.43/1.33  fof(f47,plain,(
% 7.43/1.33    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.43/1.33    inference(cnf_transformation,[],[f23])).
% 7.43/1.33  fof(f23,axiom,(
% 7.43/1.33    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 7.43/1.33  fof(f106,plain,(
% 7.43/1.33    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 7.43/1.33    inference(resolution,[],[f45,f58])).
% 7.43/1.33  fof(f58,plain,(
% 7.43/1.33    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f35])).
% 7.43/1.33  fof(f35,plain,(
% 7.43/1.33    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.43/1.33    inference(nnf_transformation,[],[f28])).
% 7.43/1.33  fof(f28,plain,(
% 7.43/1.33    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.43/1.33    inference(ennf_transformation,[],[f20])).
% 7.43/1.33  fof(f20,axiom,(
% 7.43/1.33    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 7.43/1.33  fof(f45,plain,(
% 7.43/1.33    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.43/1.33    inference(cnf_transformation,[],[f34])).
% 7.43/1.33  fof(f34,plain,(
% 7.43/1.33    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.43/1.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f33])).
% 7.43/1.33  fof(f33,plain,(
% 7.43/1.33    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 7.43/1.33    introduced(choice_axiom,[])).
% 7.43/1.33  fof(f27,plain,(
% 7.43/1.33    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.43/1.33    inference(ennf_transformation,[],[f26])).
% 7.43/1.33  fof(f26,negated_conjecture,(
% 7.43/1.33    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 7.43/1.33    inference(negated_conjecture,[],[f25])).
% 7.43/1.33  fof(f25,conjecture,(
% 7.43/1.33    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 7.43/1.33  fof(f105,plain,(
% 7.43/1.33    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 7.43/1.33    inference(resolution,[],[f45,f90])).
% 7.43/1.33  fof(f90,plain,(
% 7.43/1.33    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 7.43/1.33    inference(definition_unfolding,[],[f63,f56])).
% 7.43/1.33  fof(f56,plain,(
% 7.43/1.33    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.43/1.33    inference(cnf_transformation,[],[f4])).
% 7.43/1.33  fof(f4,axiom,(
% 7.43/1.33    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 7.43/1.33  fof(f63,plain,(
% 7.43/1.33    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.43/1.33    inference(cnf_transformation,[],[f30])).
% 7.43/1.33  fof(f30,plain,(
% 7.43/1.33    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.43/1.33    inference(ennf_transformation,[],[f22])).
% 7.43/1.33  fof(f22,axiom,(
% 7.43/1.33    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 7.43/1.33  fof(f103,plain,(
% 7.43/1.33    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 7.43/1.33    inference(forward_demodulation,[],[f46,f48])).
% 7.43/1.33  fof(f48,plain,(
% 7.43/1.33    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.43/1.33    inference(cnf_transformation,[],[f21])).
% 7.43/1.33  fof(f21,axiom,(
% 7.43/1.33    ! [X0] : k2_subset_1(X0) = X0),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 7.43/1.33  fof(f46,plain,(
% 7.43/1.33    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 7.43/1.33    inference(cnf_transformation,[],[f34])).
% 7.43/1.33  fof(f9076,plain,(
% 7.43/1.33    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 7.43/1.33    inference(forward_demodulation,[],[f8013,f50])).
% 7.43/1.33  fof(f50,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.43/1.33    inference(cnf_transformation,[],[f9])).
% 7.43/1.33  fof(f9,axiom,(
% 7.43/1.33    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 7.43/1.33  fof(f8013,plain,(
% 7.43/1.33    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 7.43/1.33    inference(backward_demodulation,[],[f7101,f7734])).
% 7.43/1.33  fof(f7734,plain,(
% 7.43/1.33    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 7.43/1.33    inference(forward_demodulation,[],[f7673,f50])).
% 7.43/1.33  fof(f7673,plain,(
% 7.43/1.33    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 7.43/1.33    inference(superposition,[],[f7036,f49])).
% 7.43/1.33  fof(f49,plain,(
% 7.43/1.33    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f7])).
% 7.43/1.33  fof(f7,axiom,(
% 7.43/1.33    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 7.43/1.33  fof(f7036,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(sK1,sK1) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 7.43/1.33    inference(duplicate_literal_removal,[],[f6992])).
% 7.43/1.33  fof(f6992,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(sK1,sK1) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) | k5_xboole_0(sK1,sK1) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 7.43/1.33    inference(resolution,[],[f2672,f2671])).
% 7.43/1.33  fof(f2671,plain,(
% 7.43/1.33    ( ! [X4,X3] : (r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,k5_xboole_0(X3,k3_xboole_0(X3,X4))),X3) | k5_xboole_0(sK1,sK1) = k5_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 7.43/1.33    inference(backward_demodulation,[],[f1226,f2630])).
% 7.43/1.33  fof(f2630,plain,(
% 7.43/1.33    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 7.43/1.33    inference(superposition,[],[f1141,f2462])).
% 7.43/1.33  fof(f2462,plain,(
% 7.43/1.33    sK1 = k3_xboole_0(sK1,sK1)),
% 7.43/1.33    inference(resolution,[],[f2460,f62])).
% 7.43/1.33  fof(f2460,plain,(
% 7.43/1.33    r1_tarski(sK1,sK1)),
% 7.43/1.33    inference(forward_demodulation,[],[f2459,f122])).
% 7.43/1.33  fof(f2459,plain,(
% 7.43/1.33    r1_tarski(k3_xboole_0(sK0,sK1),sK1)),
% 7.43/1.33    inference(forward_demodulation,[],[f2455,f52])).
% 7.43/1.33  fof(f2455,plain,(
% 7.43/1.33    r1_tarski(k3_xboole_0(sK1,sK0),sK1)),
% 7.43/1.33    inference(superposition,[],[f2424,f50])).
% 7.43/1.33  fof(f2424,plain,(
% 7.43/1.33    ( ! [X2] : (r1_tarski(k3_xboole_0(sK1,k5_xboole_0(sK0,X2)),sK1)) )),
% 7.43/1.33    inference(superposition,[],[f88,f1141])).
% 7.43/1.33  fof(f88,plain,(
% 7.43/1.33    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 7.43/1.33    inference(definition_unfolding,[],[f51,f56])).
% 7.43/1.33  fof(f51,plain,(
% 7.43/1.33    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f8])).
% 7.43/1.33  fof(f8,axiom,(
% 7.43/1.33    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 7.43/1.33  fof(f1141,plain,(
% 7.43/1.33    ( ! [X0] : (k3_xboole_0(sK1,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) )),
% 7.43/1.33    inference(superposition,[],[f152,f52])).
% 7.43/1.33  fof(f152,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f146,f52])).
% 7.43/1.33  fof(f146,plain,(
% 7.43/1.33    ( ! [X0] : (k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) )),
% 7.43/1.33    inference(superposition,[],[f70,f122])).
% 7.43/1.33  fof(f70,plain,(
% 7.43/1.33    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f5])).
% 7.43/1.33  fof(f5,axiom,(
% 7.43/1.33    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 7.43/1.33  fof(f1226,plain,(
% 7.43/1.33    ( ! [X4,X3] : (k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(X3,k3_xboole_0(X3,X4)) | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,k5_xboole_0(X3,k3_xboole_0(X3,X4))),X3)) )),
% 7.43/1.33    inference(backward_demodulation,[],[f619,f1196])).
% 7.43/1.33  fof(f1196,plain,(
% 7.43/1.33    k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 7.43/1.33    inference(resolution,[],[f424,f1154])).
% 7.43/1.33  fof(f1154,plain,(
% 7.43/1.33    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) )),
% 7.43/1.33    inference(subsumption_resolution,[],[f1147,f1146])).
% 7.43/1.33  fof(f1146,plain,(
% 7.43/1.33    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | r2_hidden(X1,sK1)) )),
% 7.43/1.33    inference(superposition,[],[f102,f152])).
% 7.43/1.33  fof(f102,plain,(
% 7.43/1.33    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 7.43/1.33    inference(equality_resolution,[],[f97])).
% 7.43/1.33  fof(f97,plain,(
% 7.43/1.33    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.43/1.33    inference(definition_unfolding,[],[f72,f56])).
% 7.43/1.33  fof(f72,plain,(
% 7.43/1.33    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.43/1.33    inference(cnf_transformation,[],[f44])).
% 7.43/1.33  fof(f44,plain,(
% 7.43/1.33    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.43/1.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 7.43/1.33  fof(f43,plain,(
% 7.43/1.33    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 7.43/1.33    introduced(choice_axiom,[])).
% 7.43/1.33  fof(f42,plain,(
% 7.43/1.33    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.43/1.33    inference(rectify,[],[f41])).
% 7.43/1.33  fof(f41,plain,(
% 7.43/1.33    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.43/1.33    inference(flattening,[],[f40])).
% 7.43/1.33  fof(f40,plain,(
% 7.43/1.33    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.43/1.33    inference(nnf_transformation,[],[f3])).
% 7.43/1.33  fof(f3,axiom,(
% 7.43/1.33    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 7.43/1.33  fof(f1147,plain,(
% 7.43/1.33    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | ~r2_hidden(X2,sK1)) )),
% 7.43/1.33    inference(superposition,[],[f101,f152])).
% 7.43/1.33  fof(f101,plain,(
% 7.43/1.33    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 7.43/1.33    inference(equality_resolution,[],[f96])).
% 7.43/1.33  fof(f96,plain,(
% 7.43/1.33    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.43/1.33    inference(definition_unfolding,[],[f73,f56])).
% 7.43/1.33  fof(f73,plain,(
% 7.43/1.33    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.43/1.33    inference(cnf_transformation,[],[f44])).
% 7.43/1.33  fof(f424,plain,(
% 7.43/1.33    ( ! [X1] : (r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1) | k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = X1) )),
% 7.43/1.33    inference(backward_demodulation,[],[f326,f415])).
% 7.43/1.33  fof(f415,plain,(
% 7.43/1.33    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 7.43/1.33    inference(superposition,[],[f142,f140])).
% 7.43/1.33  fof(f140,plain,(
% 7.43/1.33    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 7.43/1.33    inference(backward_demodulation,[],[f121,f133])).
% 7.43/1.33  fof(f121,plain,(
% 7.43/1.33    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK0)),
% 7.43/1.33    inference(resolution,[],[f118,f62])).
% 7.43/1.33  fof(f118,plain,(
% 7.43/1.33    r1_tarski(k3_subset_1(sK0,sK1),sK0)),
% 7.43/1.33    inference(superposition,[],[f88,f105])).
% 7.43/1.33  fof(f142,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(sK1,k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK1,X0))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f126,f52])).
% 7.43/1.33  fof(f126,plain,(
% 7.43/1.33    ( ! [X0] : (k3_xboole_0(k5_xboole_0(sK1,X0),sK0) = k5_xboole_0(sK1,k3_xboole_0(X0,sK0))) )),
% 7.43/1.33    inference(superposition,[],[f70,f114])).
% 7.43/1.33  fof(f326,plain,(
% 7.43/1.33    ( ! [X1] : (k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) = X1 | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1)) )),
% 7.43/1.33    inference(duplicate_literal_removal,[],[f325])).
% 7.43/1.33  fof(f325,plain,(
% 7.43/1.33    ( ! [X1] : (k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) = X1 | k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) = X1 | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1)) )),
% 7.43/1.33    inference(forward_demodulation,[],[f324,f142])).
% 7.43/1.33  fof(f324,plain,(
% 7.43/1.33    ( ! [X1] : (k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),sK0))) = X1 | k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) = X1 | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1)) )),
% 7.43/1.33    inference(forward_demodulation,[],[f323,f69])).
% 7.43/1.33  fof(f69,plain,(
% 7.43/1.33    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 7.43/1.33    inference(cnf_transformation,[],[f10])).
% 7.43/1.33  fof(f10,axiom,(
% 7.43/1.33    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 7.43/1.33  fof(f323,plain,(
% 7.43/1.33    ( ! [X1] : (k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) = X1 | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1) | k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)) = X1) )),
% 7.43/1.33    inference(forward_demodulation,[],[f322,f142])).
% 7.43/1.33  fof(f322,plain,(
% 7.43/1.33    ( ! [X1] : (r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1) | k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),sK0))) = X1 | k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)) = X1) )),
% 7.43/1.33    inference(duplicate_literal_removal,[],[f308])).
% 7.43/1.33  fof(f308,plain,(
% 7.43/1.33    ( ! [X1] : (r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1) | k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),sK0))) = X1 | k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)) = X1 | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1)) )),
% 7.43/1.33    inference(resolution,[],[f174,f93])).
% 7.43/1.33  fof(f93,plain,(
% 7.43/1.33    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 7.43/1.33    inference(definition_unfolding,[],[f76,f56])).
% 7.43/1.33  fof(f76,plain,(
% 7.43/1.33    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f44])).
% 7.43/1.33  fof(f174,plain,(
% 7.43/1.33    ( ! [X2,X3] : (r2_hidden(sK3(k5_xboole_0(sK0,sK1),X2,X3),sK0) | r2_hidden(sK3(k5_xboole_0(sK0,sK1),X2,X3),X3) | k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),X2))) = X3) )),
% 7.43/1.33    inference(forward_demodulation,[],[f173,f69])).
% 7.43/1.33  fof(f173,plain,(
% 7.43/1.33    ( ! [X2,X3] : (r2_hidden(sK3(k5_xboole_0(sK0,sK1),X2,X3),sK0) | r2_hidden(sK3(k5_xboole_0(sK0,sK1),X2,X3),X3) | k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),X2)) = X3) )),
% 7.43/1.33    inference(resolution,[],[f135,f94])).
% 7.43/1.33  fof(f94,plain,(
% 7.43/1.33    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 7.43/1.33    inference(definition_unfolding,[],[f75,f56])).
% 7.43/1.33  fof(f75,plain,(
% 7.43/1.33    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f44])).
% 7.43/1.33  fof(f135,plain,(
% 7.43/1.33    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK0,sK1)) | r2_hidden(X0,sK0)) )),
% 7.43/1.33    inference(backward_demodulation,[],[f115,f133])).
% 7.43/1.33  fof(f115,plain,(
% 7.43/1.33    ( ! [X0] : (~r2_hidden(X0,k3_subset_1(sK0,sK1)) | r2_hidden(X0,sK0)) )),
% 7.43/1.33    inference(superposition,[],[f102,f105])).
% 7.43/1.33  fof(f619,plain,(
% 7.43/1.33    ( ! [X4,X3] : (k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,k5_xboole_0(X3,k3_xboole_0(X3,X4))),X3)) )),
% 7.43/1.33    inference(resolution,[],[f424,f102])).
% 7.43/1.33  fof(f2672,plain,(
% 7.43/1.33    ( ! [X6,X5] : (~r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,k5_xboole_0(X5,k3_xboole_0(X5,X6))),X6) | k5_xboole_0(sK1,sK1) = k5_xboole_0(X5,k3_xboole_0(X5,X6))) )),
% 7.43/1.33    inference(backward_demodulation,[],[f1227,f2630])).
% 7.43/1.33  fof(f1227,plain,(
% 7.43/1.33    ( ! [X6,X5] : (k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) | ~r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,k5_xboole_0(X5,k3_xboole_0(X5,X6))),X6)) )),
% 7.43/1.33    inference(backward_demodulation,[],[f620,f1196])).
% 7.43/1.33  fof(f620,plain,(
% 7.43/1.33    ( ! [X6,X5] : (k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) | ~r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,k5_xboole_0(X5,k3_xboole_0(X5,X6))),X6)) )),
% 7.43/1.33    inference(resolution,[],[f424,f101])).
% 7.43/1.33  fof(f7101,plain,(
% 7.43/1.33    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 7.43/1.33    inference(forward_demodulation,[],[f7100,f4989])).
% 7.43/1.33  fof(f4989,plain,(
% 7.43/1.33    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 7.43/1.33    inference(backward_demodulation,[],[f4300,f4988])).
% 7.43/1.33  fof(f4988,plain,(
% 7.43/1.33    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 7.43/1.33    inference(forward_demodulation,[],[f4987,f4297])).
% 7.43/1.33  fof(f4297,plain,(
% 7.43/1.33    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 7.43/1.33    inference(backward_demodulation,[],[f515,f4265])).
% 7.43/1.33  fof(f4265,plain,(
% 7.43/1.33    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 7.43/1.33    inference(superposition,[],[f517,f416])).
% 7.43/1.33  fof(f416,plain,(
% 7.43/1.33    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 7.43/1.33    inference(superposition,[],[f142,f114])).
% 7.43/1.33  fof(f517,plain,(
% 7.43/1.33    ( ! [X1] : (k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X1))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,X1)))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f502,f142])).
% 7.43/1.33  fof(f502,plain,(
% 7.43/1.33    ( ! [X1] : (k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X1))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(X1,sK0)))) )),
% 7.43/1.33    inference(superposition,[],[f217,f69])).
% 7.43/1.33  fof(f217,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X0)))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f216,f69])).
% 7.43/1.33  fof(f216,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),X0))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f209,f52])).
% 7.43/1.33  fof(f209,plain,(
% 7.43/1.33    ( ! [X0] : (k3_xboole_0(k5_xboole_0(k5_xboole_0(sK0,sK1),X0),sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(X0,sK0))) )),
% 7.43/1.33    inference(superposition,[],[f70,f140])).
% 7.43/1.33  fof(f515,plain,(
% 7.43/1.33    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 7.43/1.33    inference(forward_demodulation,[],[f501,f53])).
% 7.43/1.33  fof(f53,plain,(
% 7.43/1.33    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f2])).
% 7.43/1.33  fof(f2,axiom,(
% 7.43/1.33    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 7.43/1.33  fof(f501,plain,(
% 7.43/1.33    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 7.43/1.33    inference(superposition,[],[f217,f114])).
% 7.43/1.33  fof(f4987,plain,(
% 7.43/1.33    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 7.43/1.33    inference(forward_demodulation,[],[f4986,f53])).
% 7.43/1.33  fof(f4986,plain,(
% 7.43/1.33    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK0))),
% 7.43/1.33    inference(forward_demodulation,[],[f4985,f3442])).
% 7.43/1.33  fof(f3442,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(X0,k4_subset_1(sK0,sK1,sK1)))) )),
% 7.43/1.33    inference(superposition,[],[f3337,f53])).
% 7.43/1.33  fof(f3337,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0))) )),
% 7.43/1.33    inference(backward_demodulation,[],[f2618,f3336])).
% 7.43/1.33  fof(f3336,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,X0))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f3330,f69])).
% 7.43/1.33  fof(f3330,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,sK1),X0) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,X0))) )),
% 7.43/1.33    inference(superposition,[],[f69,f3303])).
% 7.43/1.33  fof(f3303,plain,(
% 7.43/1.33    k5_xboole_0(sK1,sK1) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1)),
% 7.43/1.33    inference(forward_demodulation,[],[f3291,f3301])).
% 7.43/1.33  fof(f3301,plain,(
% 7.43/1.33    k5_xboole_0(sK1,sK1) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK1,sK1))),
% 7.43/1.33    inference(forward_demodulation,[],[f3300,f3157])).
% 7.43/1.33  fof(f3157,plain,(
% 7.43/1.33    k5_xboole_0(sK1,sK1) = k5_xboole_0(sK1,k4_subset_1(sK0,sK1,sK1))),
% 7.43/1.33    inference(resolution,[],[f3083,f2664])).
% 7.43/1.33  fof(f2664,plain,(
% 7.43/1.33    ( ! [X1] : (r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1) | k5_xboole_0(sK1,sK1) = X1) )),
% 7.43/1.33    inference(backward_demodulation,[],[f1212,f2630])).
% 7.43/1.33  fof(f1212,plain,(
% 7.43/1.33    ( ! [X1] : (r2_hidden(sK3(k5_xboole_0(sK0,sK1),sK0,X1),X1) | k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = X1) )),
% 7.43/1.33    inference(backward_demodulation,[],[f424,f1196])).
% 7.43/1.33  fof(f3083,plain,(
% 7.43/1.33    ( ! [X3] : (~r2_hidden(X3,k5_xboole_0(sK1,k4_subset_1(sK0,sK1,sK1)))) )),
% 7.43/1.33    inference(global_subsumption,[],[f2496,f2653])).
% 7.43/1.33  fof(f2653,plain,(
% 7.43/1.33    ( ! [X2] : (~r2_hidden(X2,k5_xboole_0(sK1,sK1))) )),
% 7.43/1.33    inference(backward_demodulation,[],[f1154,f2630])).
% 7.43/1.33  fof(f2496,plain,(
% 7.43/1.33    ( ! [X4] : (~r2_hidden(X4,k5_xboole_0(sK1,k4_subset_1(sK0,sK1,sK1))) | r2_hidden(X4,k5_xboole_0(sK1,sK1))) )),
% 7.43/1.33    inference(backward_demodulation,[],[f306,f2463])).
% 7.43/1.33  fof(f2463,plain,(
% 7.43/1.33    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 7.43/1.33    inference(backward_demodulation,[],[f159,f2462])).
% 7.43/1.33  fof(f159,plain,(
% 7.43/1.33    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(k3_xboole_0(sK1,sK1),k5_xboole_0(sK1,sK1))),
% 7.43/1.33    inference(resolution,[],[f109,f45])).
% 7.43/1.33  fof(f109,plain,(
% 7.43/1.33    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k5_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(X0,sK1))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f108,f53])).
% 7.43/1.33  fof(f108,plain,(
% 7.43/1.33    ( ! [X0] : (k4_subset_1(sK0,X0,sK1) = k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f104,f89])).
% 7.43/1.33  fof(f89,plain,(
% 7.43/1.33    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.43/1.33    inference(definition_unfolding,[],[f57,f87])).
% 7.43/1.33  fof(f87,plain,(
% 7.43/1.33    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.43/1.33    inference(definition_unfolding,[],[f54,f86])).
% 7.43/1.33  fof(f86,plain,(
% 7.43/1.33    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.43/1.33    inference(definition_unfolding,[],[f55,f85])).
% 7.43/1.33  fof(f85,plain,(
% 7.43/1.33    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.43/1.33    inference(definition_unfolding,[],[f68,f84])).
% 7.43/1.33  fof(f84,plain,(
% 7.43/1.33    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.43/1.33    inference(definition_unfolding,[],[f78,f83])).
% 7.43/1.33  fof(f83,plain,(
% 7.43/1.33    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.43/1.33    inference(definition_unfolding,[],[f79,f82])).
% 7.43/1.33  fof(f82,plain,(
% 7.43/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.43/1.33    inference(definition_unfolding,[],[f80,f81])).
% 7.43/1.33  fof(f81,plain,(
% 7.43/1.33    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f17])).
% 7.43/1.33  fof(f17,axiom,(
% 7.43/1.33    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 7.43/1.33  fof(f80,plain,(
% 7.43/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f16])).
% 7.43/1.33  fof(f16,axiom,(
% 7.43/1.33    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 7.43/1.33  fof(f79,plain,(
% 7.43/1.33    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f15])).
% 7.43/1.33  fof(f15,axiom,(
% 7.43/1.33    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 7.43/1.33  fof(f78,plain,(
% 7.43/1.33    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f14])).
% 7.43/1.33  fof(f14,axiom,(
% 7.43/1.33    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 7.43/1.33  fof(f68,plain,(
% 7.43/1.33    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f13])).
% 7.43/1.33  fof(f13,axiom,(
% 7.43/1.33    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 7.43/1.33  fof(f55,plain,(
% 7.43/1.33    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f12])).
% 7.43/1.33  fof(f12,axiom,(
% 7.43/1.33    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 7.43/1.33  fof(f54,plain,(
% 7.43/1.33    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.43/1.33    inference(cnf_transformation,[],[f19])).
% 7.43/1.33  fof(f19,axiom,(
% 7.43/1.33    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 7.43/1.33  fof(f57,plain,(
% 7.43/1.33    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 7.43/1.33    inference(cnf_transformation,[],[f11])).
% 7.43/1.33  fof(f11,axiom,(
% 7.43/1.33    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 7.43/1.33  fof(f104,plain,(
% 7.43/1.33    ( ! [X0] : (k4_subset_1(sK0,X0,sK1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 7.43/1.33    inference(resolution,[],[f45,f91])).
% 7.43/1.33  fof(f91,plain,(
% 7.43/1.33    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.43/1.33    inference(definition_unfolding,[],[f71,f87])).
% 7.43/1.33  fof(f71,plain,(
% 7.43/1.33    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.43/1.33    inference(cnf_transformation,[],[f32])).
% 7.43/1.33  fof(f32,plain,(
% 7.43/1.33    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.43/1.33    inference(flattening,[],[f31])).
% 7.43/1.33  fof(f31,plain,(
% 7.43/1.33    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.43/1.33    inference(ennf_transformation,[],[f24])).
% 7.43/1.33  fof(f24,axiom,(
% 7.43/1.33    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 7.43/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 7.43/1.33  fof(f306,plain,(
% 7.43/1.33    ( ! [X4] : (~r2_hidden(X4,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) | r2_hidden(X4,k5_xboole_0(sK1,sK1))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f299,f69])).
% 7.43/1.33  fof(f299,plain,(
% 7.43/1.33    ( ! [X4] : (~r2_hidden(X4,k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,sK1))) | r2_hidden(X4,k5_xboole_0(sK1,sK1))) )),
% 7.43/1.33    inference(superposition,[],[f102,f155])).
% 7.43/1.33  fof(f155,plain,(
% 7.43/1.33    k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1)),
% 7.43/1.33    inference(resolution,[],[f128,f62])).
% 7.43/1.33  fof(f128,plain,(
% 7.43/1.33    r1_tarski(k5_xboole_0(sK1,sK1),sK1)),
% 7.43/1.33    inference(superposition,[],[f88,f114])).
% 7.43/1.33  fof(f3300,plain,(
% 7.43/1.33    k5_xboole_0(sK1,k4_subset_1(sK0,sK1,sK1)) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK1,sK1))),
% 7.43/1.33    inference(forward_demodulation,[],[f3290,f53])).
% 7.43/1.33  fof(f3290,plain,(
% 7.43/1.33    k5_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK1,sK1))),
% 7.43/1.33    inference(superposition,[],[f3262,f2465])).
% 7.43/1.33  fof(f2465,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(X0,sK1)))) )),
% 7.43/1.33    inference(backward_demodulation,[],[f233,f2462])).
% 7.43/1.33  fof(f233,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) = k5_xboole_0(k3_xboole_0(sK1,sK1),k5_xboole_0(sK1,k5_xboole_0(X0,sK1)))) )),
% 7.43/1.33    inference(superposition,[],[f201,f53])).
% 7.43/1.33  fof(f201,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) = k5_xboole_0(k3_xboole_0(sK1,sK1),k5_xboole_0(sK1,k5_xboole_0(sK1,X0)))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f200,f69])).
% 7.43/1.33  fof(f200,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK1,sK1),k5_xboole_0(k5_xboole_0(sK1,sK1),X0)) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0)) )),
% 7.43/1.33    inference(superposition,[],[f69,f159])).
% 7.43/1.33  fof(f3262,plain,(
% 7.43/1.33    ( ! [X5] : (k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X5) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X5)))) )),
% 7.43/1.33    inference(backward_demodulation,[],[f2613,f3261])).
% 7.43/1.33  fof(f3261,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,k5_xboole_0(sK1,X0)))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f3240,f69])).
% 7.43/1.33  fof(f3240,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(k5_xboole_0(sK1,sK1),X0))) )),
% 7.43/1.33    inference(superposition,[],[f69,f3198])).
% 7.43/1.33  fof(f3198,plain,(
% 7.43/1.33    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,sK1))),
% 7.43/1.33    inference(forward_demodulation,[],[f3177,f2463])).
% 7.43/1.33  fof(f3177,plain,(
% 7.43/1.33    k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,sK1))),
% 7.43/1.33    inference(backward_demodulation,[],[f2612,f3157])).
% 7.43/1.33  fof(f2612,plain,(
% 7.43/1.33    k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_subset_1(sK0,sK1,sK1)))),
% 7.43/1.33    inference(superposition,[],[f2464,f2463])).
% 7.43/1.33  fof(f2464,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,X0)))) )),
% 7.43/1.33    inference(backward_demodulation,[],[f201,f2462])).
% 7.43/1.33  fof(f2613,plain,(
% 7.43/1.33    ( ! [X5] : (k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,k5_xboole_0(sK1,X5))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X5)))) )),
% 7.43/1.33    inference(superposition,[],[f2464,f2464])).
% 7.43/1.33  fof(f3291,plain,(
% 7.43/1.33    k5_xboole_0(k4_subset_1(sK0,sK1,sK1),sK1) = k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK1,sK1))),
% 7.43/1.33    inference(superposition,[],[f2465,f3262])).
% 7.43/1.33  fof(f2618,plain,(
% 7.43/1.33    ( ! [X0] : (k5_xboole_0(k4_subset_1(sK0,sK1,sK1),k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(k4_subset_1(sK0,sK1,sK1),X0))) )),
% 7.43/1.33    inference(superposition,[],[f2464,f2464])).
% 7.43/1.33  fof(f4985,plain,(
% 7.43/1.33    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK1,k5_xboole_0(sK0,k4_subset_1(sK0,sK1,sK1)))),
% 7.43/1.33    inference(forward_demodulation,[],[f4981,f4308])).
% 7.43/1.33  fof(f4308,plain,(
% 7.43/1.33    k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))) = k5_xboole_0(sK0,k4_subset_1(sK0,sK1,sK1))),
% 7.43/1.33    inference(backward_demodulation,[],[f3619,f4297])).
% 7.43/1.33  fof(f3619,plain,(
% 7.43/1.33    k5_xboole_0(sK0,k4_subset_1(sK0,sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 7.43/1.33    inference(forward_demodulation,[],[f3594,f3618])).
% 7.43/1.33  fof(f3618,plain,(
% 7.43/1.33    k5_xboole_0(sK0,k4_subset_1(sK0,sK1,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))))),
% 7.43/1.33    inference(forward_demodulation,[],[f3617,f53])).
% 7.43/1.33  fof(f3617,plain,(
% 7.43/1.33    k5_xboole_0(k4_subset_1(sK0,sK1,sK1),sK0) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))))),
% 7.43/1.33    inference(forward_demodulation,[],[f3616,f2465])).
% 7.43/1.33  fof(f3616,plain,(
% 7.43/1.33    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))))),
% 7.43/1.33    inference(forward_demodulation,[],[f3615,f53])).
% 7.43/1.33  fof(f3615,plain,(
% 7.43/1.33    k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))))),
% 7.43/1.33    inference(forward_demodulation,[],[f3593,f53])).
% 7.43/1.33  fof(f3593,plain,(
% 7.43/1.33    k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),sK1))),
% 7.43/1.33    inference(superposition,[],[f434,f515])).
% 7.43/1.33  fof(f434,plain,(
% 7.43/1.33    ( ! [X0] : (k3_xboole_0(sK0,k5_xboole_0(X0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,X0),sK1)) )),
% 7.43/1.33    inference(superposition,[],[f143,f52])).
% 7.43/1.33  fof(f143,plain,(
% 7.43/1.33    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,sK0),sK1) = k3_xboole_0(sK0,k5_xboole_0(X1,sK1))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f127,f52])).
% 7.43/1.33  fof(f127,plain,(
% 7.43/1.33    ( ! [X1] : (k3_xboole_0(k5_xboole_0(X1,sK1),sK0) = k5_xboole_0(k3_xboole_0(X1,sK0),sK1)) )),
% 7.43/1.33    inference(superposition,[],[f70,f114])).
% 7.43/1.33  fof(f3594,plain,(
% 7.43/1.33    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))))),
% 7.43/1.33    inference(superposition,[],[f413,f515])).
% 7.43/1.33  fof(f413,plain,(
% 7.43/1.33    ( ! [X0] : (k3_xboole_0(sK0,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k3_xboole_0(sK0,X0))) )),
% 7.43/1.33    inference(superposition,[],[f142,f52])).
% 7.43/1.33  fof(f4981,plain,(
% 7.43/1.33    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))))),
% 7.43/1.33    inference(superposition,[],[f4300,f69])).
% 7.43/1.33  fof(f4300,plain,(
% 7.43/1.33    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 7.43/1.33    inference(backward_demodulation,[],[f2650,f4297])).
% 7.43/1.33  fof(f2650,plain,(
% 7.43/1.33    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 7.43/1.33    inference(backward_demodulation,[],[f166,f2630])).
% 7.43/1.33  fof(f166,plain,(
% 7.43/1.33    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 7.43/1.33    inference(forward_demodulation,[],[f165,f52])).
% 7.43/1.33  fof(f165,plain,(
% 7.43/1.33    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 7.43/1.33    inference(forward_demodulation,[],[f160,f53])).
% 7.43/1.33  fof(f160,plain,(
% 7.43/1.33    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),sK1))),
% 7.43/1.33    inference(resolution,[],[f158,f109])).
% 7.43/1.33  fof(f158,plain,(
% 7.43/1.33    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 7.43/1.33    inference(subsumption_resolution,[],[f157,f47])).
% 7.43/1.33  fof(f157,plain,(
% 7.43/1.33    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 7.43/1.33    inference(resolution,[],[f139,f59])).
% 7.43/1.33  fof(f59,plain,(
% 7.43/1.33    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.43/1.33    inference(cnf_transformation,[],[f35])).
% 7.43/1.33  fof(f139,plain,(
% 7.43/1.33    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 7.43/1.33    inference(backward_demodulation,[],[f120,f133])).
% 7.43/1.33  fof(f120,plain,(
% 7.43/1.33    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 7.43/1.33    inference(resolution,[],[f118,f98])).
% 7.43/1.33  fof(f98,plain,(
% 7.43/1.33    ( ! [X0,X3] : (~r1_tarski(X3,X0) | r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.43/1.33    inference(equality_resolution,[],[f65])).
% 7.43/1.33  fof(f65,plain,(
% 7.43/1.33    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.43/1.33    inference(cnf_transformation,[],[f39])).
% 7.43/1.33  fof(f7100,plain,(
% 7.43/1.33    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 7.43/1.33    inference(forward_demodulation,[],[f7099,f2630])).
% 7.43/1.33  fof(f7099,plain,(
% 7.43/1.33    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 7.43/1.33    inference(forward_demodulation,[],[f7090,f4297])).
% 7.43/1.33  fof(f7090,plain,(
% 7.43/1.33    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 7.43/1.33    inference(resolution,[],[f168,f45])).
% 7.43/1.33  fof(f168,plain,(
% 7.43/1.33    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,sK1)),k5_xboole_0(X0,k5_xboole_0(sK0,sK1)))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f167,f53])).
% 7.43/1.33  fof(f167,plain,(
% 7.43/1.33    ( ! [X0] : (k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK0,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 7.43/1.33    inference(forward_demodulation,[],[f161,f89])).
% 7.43/1.33  fof(f161,plain,(
% 7.43/1.33    ( ! [X0] : (k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 7.43/1.33    inference(resolution,[],[f158,f91])).
% 7.43/1.33  % SZS output end Proof for theBenchmark
% 7.43/1.33  % (13186)------------------------------
% 7.43/1.33  % (13186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.43/1.33  % (13186)Termination reason: Refutation
% 7.43/1.33  
% 7.43/1.33  % (13186)Memory used [KB]: 16630
% 7.43/1.33  % (13186)Time elapsed: 0.887 s
% 7.43/1.33  % (13186)------------------------------
% 7.43/1.33  % (13186)------------------------------
% 7.43/1.34  % (13177)Success in time 0.962 s
%------------------------------------------------------------------------------
