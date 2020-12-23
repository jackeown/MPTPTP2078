%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:03 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 244 expanded)
%              Number of leaves         :   19 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  175 ( 538 expanded)
%              Number of equality atoms :   68 ( 202 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f455,plain,(
    $false ),
    inference(subsumption_resolution,[],[f454,f63])).

fof(f63,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f32,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f32,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f454,plain,(
    sK0 = k4_subset_1(sK0,sK1,sK0) ),
    inference(forward_demodulation,[],[f453,f191])).

fof(f191,plain,(
    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f187,f158])).

fof(f158,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f85,f155])).

fof(f155,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f137,f93])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f91,f92])).

fof(f92,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f85,f48])).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f91,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f55,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f58,f74])).

fof(f74,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f71,f62])).

fof(f62,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f71,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f68,f45])).

fof(f45,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f36,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f137,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f60,f48])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f54,f51,f51])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f85,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f55,f48])).

fof(f187,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f57,f161])).

fof(f161,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f90,f157])).

fof(f157,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f89,f155])).

fof(f89,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f55,f80])).

fof(f80,plain,(
    ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(resolution,[],[f58,f75])).

fof(f75,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(resolution,[],[f72,f62])).

fof(f72,plain,(
    ! [X1] : r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(subsumption_resolution,[],[f69,f45])).

fof(f69,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f36,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f34,f35])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f90,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f55,f78])).

fof(f78,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f58,f73])).

fof(f73,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f70,f62])).

fof(f70,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f67,f45])).

fof(f67,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f36,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f46,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f453,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f449,f59])).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f53,f52,f52])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f449,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK0)) ),
    inference(resolution,[],[f426,f64])).

fof(f426,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,sK1,X0) = k3_tarski(k1_enumset1(sK1,sK1,X0)) ) ),
    inference(resolution,[],[f65,f31])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) ) ),
    inference(backward_demodulation,[],[f56,f57])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.44  % (1783)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.47  % (1802)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.47  % (1783)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % (1793)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.48  % (1802)Refutation not found, incomplete strategy% (1802)------------------------------
% 0.19/0.48  % (1802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f455,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(subsumption_resolution,[],[f454,f63])).
% 0.19/0.48  fof(f63,plain,(
% 0.19/0.48    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 0.19/0.48    inference(backward_demodulation,[],[f32,f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,axiom,(
% 0.19/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.19/0.48    inference(cnf_transformation,[],[f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f18])).
% 0.19/0.48  fof(f18,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.19/0.48    inference(negated_conjecture,[],[f17])).
% 0.19/0.48  fof(f17,conjecture,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 0.19/0.48  fof(f454,plain,(
% 0.19/0.48    sK0 = k4_subset_1(sK0,sK1,sK0)),
% 0.19/0.48    inference(forward_demodulation,[],[f453,f191])).
% 0.19/0.48  fof(f191,plain,(
% 0.19/0.48    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 0.19/0.48    inference(forward_demodulation,[],[f187,f158])).
% 0.19/0.48  fof(f158,plain,(
% 0.19/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.48    inference(backward_demodulation,[],[f85,f155])).
% 0.19/0.48  fof(f155,plain,(
% 0.19/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.19/0.48    inference(forward_demodulation,[],[f137,f93])).
% 0.19/0.48  fof(f93,plain,(
% 0.19/0.48    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.19/0.48    inference(backward_demodulation,[],[f91,f92])).
% 0.19/0.49  fof(f92,plain,(
% 0.19/0.49    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.49    inference(superposition,[],[f85,f48])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.49  fof(f91,plain,(
% 0.19/0.49    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 0.19/0.49    inference(superposition,[],[f55,f79])).
% 0.19/0.49  fof(f79,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.19/0.49    inference(resolution,[],[f58,f74])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.49    inference(resolution,[],[f71,f62])).
% 0.19/0.49  fof(f62,plain,(
% 0.19/0.49    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f41])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.49    inference(rectify,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.49    inference(nnf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.49  fof(f71,plain,(
% 0.19/0.49    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f68,f45])).
% 0.19/0.49  fof(f45,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,axiom,(
% 0.19/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.19/0.49  fof(f68,plain,(
% 0.19/0.49    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(resolution,[],[f36,f40])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,axiom,(
% 0.19/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.19/0.49    inference(nnf_transformation,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,axiom,(
% 0.19/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.19/0.49    inference(definition_unfolding,[],[f49,f51])).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.19/0.49    inference(definition_unfolding,[],[f50,f51])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.49  fof(f137,plain,(
% 0.19/0.49    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.19/0.49    inference(superposition,[],[f60,f48])).
% 0.19/0.49  fof(f60,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.19/0.49    inference(definition_unfolding,[],[f54,f51,f51])).
% 0.19/0.49  fof(f54,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.49  fof(f85,plain,(
% 0.19/0.49    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.19/0.49    inference(superposition,[],[f55,f48])).
% 0.19/0.49  fof(f187,plain,(
% 0.19/0.49    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 0.19/0.49    inference(superposition,[],[f57,f161])).
% 0.19/0.49  fof(f161,plain,(
% 0.19/0.49    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.19/0.49    inference(backward_demodulation,[],[f90,f157])).
% 0.19/0.49  fof(f157,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.19/0.49    inference(backward_demodulation,[],[f89,f155])).
% 0.19/0.49  fof(f89,plain,(
% 0.19/0.49    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 0.19/0.49    inference(superposition,[],[f55,f80])).
% 0.19/0.49  fof(f80,plain,(
% 0.19/0.49    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 0.19/0.49    inference(resolution,[],[f58,f75])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.19/0.49    inference(resolution,[],[f72,f62])).
% 0.19/0.49  fof(f72,plain,(
% 0.19/0.49    ( ! [X1] : (r2_hidden(X1,k1_zfmisc_1(X1))) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f69,f45])).
% 0.19/0.49  fof(f69,plain,(
% 0.19/0.49    ( ! [X1] : (r2_hidden(X1,k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1))) )),
% 0.19/0.49    inference(resolution,[],[f36,f64])).
% 0.19/0.49  fof(f64,plain,(
% 0.19/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(backward_demodulation,[],[f34,f35])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,axiom,(
% 0.19/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.19/0.49  fof(f90,plain,(
% 0.19/0.49    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 0.19/0.49    inference(superposition,[],[f55,f78])).
% 0.19/0.49  fof(f78,plain,(
% 0.19/0.49    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 0.19/0.49    inference(resolution,[],[f58,f73])).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    r1_tarski(sK1,sK0)),
% 0.19/0.49    inference(resolution,[],[f70,f62])).
% 0.19/0.49  fof(f70,plain,(
% 0.19/0.49    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.49    inference(subsumption_resolution,[],[f67,f45])).
% 0.19/0.49  fof(f67,plain,(
% 0.19/0.49    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.19/0.49    inference(resolution,[],[f36,f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.49    inference(cnf_transformation,[],[f25])).
% 0.19/0.49  fof(f57,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.19/0.49    inference(definition_unfolding,[],[f47,f46,f52])).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,axiom,(
% 0.19/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.19/0.49  fof(f453,plain,(
% 0.19/0.49    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 0.19/0.49    inference(forward_demodulation,[],[f449,f59])).
% 0.19/0.49  fof(f59,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f53,f52,f52])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.19/0.49  fof(f449,plain,(
% 0.19/0.49    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK0))),
% 0.19/0.49    inference(resolution,[],[f426,f64])).
% 0.19/0.49  fof(f426,plain,(
% 0.19/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k3_tarski(k1_enumset1(sK1,sK1,X0))) )),
% 0.19/0.49    inference(resolution,[],[f65,f31])).
% 0.19/0.49  fof(f65,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))) )),
% 0.19/0.49    inference(backward_demodulation,[],[f56,f57])).
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(definition_unfolding,[],[f33,f46])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.49    inference(flattening,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.19/0.49    inference(ennf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (1783)------------------------------
% 0.19/0.49  % (1783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (1783)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (1783)Memory used [KB]: 6524
% 0.19/0.49  % (1783)Time elapsed: 0.101 s
% 0.19/0.49  % (1783)------------------------------
% 0.19/0.49  % (1783)------------------------------
% 0.19/0.49  % (1777)Success in time 0.139 s
%------------------------------------------------------------------------------
