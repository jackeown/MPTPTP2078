%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:19 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 340 expanded)
%              Number of leaves         :   24 ( 100 expanded)
%              Depth                    :   24
%              Number of atoms          :  275 (1089 expanded)
%              Number of equality atoms :   48 ( 120 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2224,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2223,f1245])).

fof(f1245,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f618,f1200])).

fof(f1200,plain,(
    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f588,f759])).

fof(f759,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f758,f183])).

fof(f183,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f182,f52])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f182,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f57,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f758,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[],[f58,f754])).

fof(f754,plain,(
    k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f750,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f750,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    inference(resolution,[],[f749,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f749,plain,(
    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f745,f99])).

fof(f99,plain,(
    ! [X6,X4,X5] :
      ( r1_xboole_0(k4_xboole_0(X6,X5),X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f72,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f745,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f619,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f619,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f616,f611])).

fof(f611,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f66,f47])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f35,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f616,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f48,f610])).

fof(f610,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f66,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f588,plain,(
    ! [X4,X2,X3] : r1_tarski(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4)) ),
    inference(resolution,[],[f73,f54])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f618,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f617,f611])).

fof(f617,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f49,f610])).

fof(f49,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f2223,plain,(
    r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f783,f2217])).

fof(f2217,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f612,f766])).

fof(f766,plain,(
    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f761,f611])).

fof(f761,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f67,f47])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f612,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[],[f66,f78])).

fof(f78,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f55,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f55,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f783,plain,(
    r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(superposition,[],[f592,f779])).

fof(f779,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f778,f183])).

fof(f778,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f58,f774])).

fof(f774,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f752,f53])).

fof(f752,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f748,f64])).

fof(f748,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f744,f72])).

fof(f744,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f619,f255])).

fof(f255,plain,(
    ! [X19,X20,X18] :
      ( ~ r1_tarski(X20,k4_xboole_0(X19,X18))
      | r1_xboole_0(X18,X20) ) ),
    inference(superposition,[],[f99,f240])).

fof(f240,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(forward_demodulation,[],[f239,f183])).

fof(f239,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f58,f223])).

fof(f223,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f207,f53])).

fof(f207,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(resolution,[],[f199,f64])).

fof(f199,plain,(
    ! [X19,X18] : r1_xboole_0(X19,k4_xboole_0(X18,X19)) ),
    inference(superposition,[],[f172,f187])).

fof(f187,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f185,f183])).

fof(f185,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f58,f166])).

fof(f166,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f158,f53])).

fof(f158,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f157,f64])).

fof(f157,plain,(
    ! [X2] : r1_xboole_0(X2,k1_xboole_0) ),
    inference(resolution,[],[f150,f65])).

fof(f150,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f149,f79])).

fof(f79,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f54,f51])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | r1_xboole_0(X1,X0) ) ),
    inference(superposition,[],[f75,f51])).

fof(f172,plain,(
    ! [X6,X4,X5] : r1_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,X4),X6)) ),
    inference(resolution,[],[f147,f65])).

fof(f147,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) ),
    inference(resolution,[],[f75,f54])).

fof(f592,plain,(
    ! [X15] : r1_tarski(k4_xboole_0(sK1,X15),k4_xboole_0(sK0,X15)) ),
    inference(resolution,[],[f73,f91])).

fof(f91,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f87,f77])).

fof(f77,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f87,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f83,f50])).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f83,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (13845)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.49  % (13842)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.49  % (13835)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (13839)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (13840)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (13836)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (13844)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (13866)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.23/0.51  % (13853)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.23/0.51  % (13854)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.23/0.51  % (13837)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.51  % (13853)Refutation not found, incomplete strategy% (13853)------------------------------
% 1.23/0.51  % (13853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.51  % (13864)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.23/0.51  % (13853)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.51  
% 1.23/0.51  % (13853)Memory used [KB]: 10618
% 1.23/0.51  % (13853)Time elapsed: 0.119 s
% 1.23/0.51  % (13853)------------------------------
% 1.23/0.51  % (13853)------------------------------
% 1.23/0.51  % (13857)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.23/0.52  % (13859)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.23/0.52  % (13855)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.23/0.52  % (13862)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.23/0.52  % (13850)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.23/0.52  % (13847)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.23/0.52  % (13849)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.23/0.52  % (13848)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.52  % (13846)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.23/0.52  % (13863)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.23/0.52  % (13838)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.23/0.52  % (13843)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.32/0.53  % (13851)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.53  % (13858)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.53  % (13861)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.54  % (13858)Refutation not found, incomplete strategy% (13858)------------------------------
% 1.32/0.54  % (13858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (13852)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.54  % (13860)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.55  % (13856)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.55  % (13858)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (13858)Memory used [KB]: 10746
% 1.32/0.55  % (13858)Time elapsed: 0.140 s
% 1.32/0.55  % (13858)------------------------------
% 1.32/0.55  % (13858)------------------------------
% 2.10/0.63  % (13949)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.10/0.65  % (13843)Refutation found. Thanks to Tanya!
% 2.10/0.65  % SZS status Theorem for theBenchmark
% 2.10/0.65  % SZS output start Proof for theBenchmark
% 2.10/0.65  fof(f2224,plain,(
% 2.10/0.65    $false),
% 2.10/0.65    inference(subsumption_resolution,[],[f2223,f1245])).
% 2.10/0.65  fof(f1245,plain,(
% 2.10/0.65    ~r1_tarski(sK1,sK2)),
% 2.10/0.65    inference(subsumption_resolution,[],[f618,f1200])).
% 2.10/0.65  fof(f1200,plain,(
% 2.10/0.65    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 2.10/0.65    inference(superposition,[],[f588,f759])).
% 2.10/0.65  fof(f759,plain,(
% 2.10/0.65    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 2.10/0.65    inference(forward_demodulation,[],[f758,f183])).
% 2.10/0.65  fof(f183,plain,(
% 2.10/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.10/0.65    inference(forward_demodulation,[],[f182,f52])).
% 2.10/0.65  fof(f52,plain,(
% 2.10/0.65    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.10/0.65    inference(cnf_transformation,[],[f6])).
% 2.10/0.65  fof(f6,axiom,(
% 2.10/0.65    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.10/0.65  fof(f182,plain,(
% 2.10/0.65    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 2.10/0.65    inference(superposition,[],[f57,f51])).
% 2.10/0.65  fof(f51,plain,(
% 2.10/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f9])).
% 2.10/0.65  fof(f9,axiom,(
% 2.10/0.65    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 2.10/0.65  fof(f57,plain,(
% 2.10/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f11])).
% 2.10/0.65  fof(f11,axiom,(
% 2.10/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.10/0.65  fof(f758,plain,(
% 2.10/0.65    k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 2.10/0.65    inference(superposition,[],[f58,f754])).
% 2.10/0.65  fof(f754,plain,(
% 2.10/0.65    k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 2.10/0.65    inference(resolution,[],[f750,f53])).
% 2.10/0.65  fof(f53,plain,(
% 2.10/0.65    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.10/0.65    inference(cnf_transformation,[],[f38])).
% 2.10/0.65  fof(f38,plain,(
% 2.10/0.65    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.10/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f37])).
% 2.10/0.65  fof(f37,plain,(
% 2.10/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.10/0.65    introduced(choice_axiom,[])).
% 2.10/0.65  fof(f23,plain,(
% 2.10/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.10/0.65    inference(ennf_transformation,[],[f3])).
% 2.10/0.65  fof(f3,axiom,(
% 2.10/0.65    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.10/0.65  fof(f750,plain,(
% 2.10/0.65    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k4_xboole_0(sK0,sK2),sK1))) )),
% 2.10/0.65    inference(resolution,[],[f749,f64])).
% 2.10/0.65  fof(f64,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f41])).
% 2.10/0.65  fof(f41,plain,(
% 2.10/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.10/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f40])).
% 2.10/0.65  fof(f40,plain,(
% 2.10/0.65    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.10/0.65    introduced(choice_axiom,[])).
% 2.10/0.65  fof(f25,plain,(
% 2.10/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.10/0.65    inference(ennf_transformation,[],[f21])).
% 2.10/0.65  fof(f21,plain,(
% 2.10/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.10/0.65    inference(rectify,[],[f2])).
% 2.10/0.65  fof(f2,axiom,(
% 2.10/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.10/0.65  fof(f749,plain,(
% 2.10/0.65    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 2.10/0.65    inference(subsumption_resolution,[],[f745,f99])).
% 2.10/0.65  fof(f99,plain,(
% 2.10/0.65    ( ! [X6,X4,X5] : (r1_xboole_0(k4_xboole_0(X6,X5),X4) | ~r1_tarski(X4,X5)) )),
% 2.10/0.65    inference(resolution,[],[f72,f65])).
% 2.10/0.65  fof(f65,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f26])).
% 2.10/0.65  fof(f26,plain,(
% 2.10/0.65    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.10/0.65    inference(ennf_transformation,[],[f1])).
% 2.10/0.65  fof(f1,axiom,(
% 2.10/0.65    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.10/0.65  fof(f72,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f29])).
% 2.10/0.65  fof(f29,plain,(
% 2.10/0.65    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.10/0.65    inference(ennf_transformation,[],[f10])).
% 2.10/0.65  fof(f10,axiom,(
% 2.10/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.10/0.65  fof(f745,plain,(
% 2.10/0.65    r1_tarski(sK1,sK2) | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 2.10/0.65    inference(resolution,[],[f619,f75])).
% 2.10/0.65  fof(f75,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f31])).
% 2.10/0.65  fof(f31,plain,(
% 2.10/0.65    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.10/0.65    inference(ennf_transformation,[],[f5])).
% 2.10/0.65  fof(f5,axiom,(
% 2.10/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.10/0.65  fof(f619,plain,(
% 2.10/0.65    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 2.10/0.65    inference(backward_demodulation,[],[f616,f611])).
% 2.10/0.65  fof(f611,plain,(
% 2.10/0.65    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 2.10/0.65    inference(resolution,[],[f66,f47])).
% 2.10/0.65  fof(f47,plain,(
% 2.10/0.65    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.10/0.65    inference(cnf_transformation,[],[f36])).
% 2.10/0.65  fof(f36,plain,(
% 2.10/0.65    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.10/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f35,f34])).
% 2.10/0.65  fof(f34,plain,(
% 2.10/0.65    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.10/0.65    introduced(choice_axiom,[])).
% 2.10/0.65  fof(f35,plain,(
% 2.10/0.65    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 2.10/0.65    introduced(choice_axiom,[])).
% 2.10/0.65  fof(f33,plain,(
% 2.10/0.65    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.65    inference(flattening,[],[f32])).
% 2.10/0.65  fof(f32,plain,(
% 2.10/0.65    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.65    inference(nnf_transformation,[],[f22])).
% 2.10/0.65  fof(f22,plain,(
% 2.10/0.65    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.65    inference(ennf_transformation,[],[f20])).
% 2.10/0.65  fof(f20,negated_conjecture,(
% 2.10/0.65    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 2.10/0.65    inference(negated_conjecture,[],[f19])).
% 2.10/0.65  fof(f19,conjecture,(
% 2.10/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 2.10/0.65  fof(f66,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f27])).
% 2.10/0.65  fof(f27,plain,(
% 2.10/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.65    inference(ennf_transformation,[],[f14])).
% 2.10/0.65  fof(f14,axiom,(
% 2.10/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.10/0.65  fof(f616,plain,(
% 2.10/0.65    r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 2.10/0.65    inference(backward_demodulation,[],[f48,f610])).
% 2.10/0.65  fof(f610,plain,(
% 2.10/0.65    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.10/0.65    inference(resolution,[],[f66,f46])).
% 2.10/0.65  fof(f46,plain,(
% 2.10/0.65    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.10/0.65    inference(cnf_transformation,[],[f36])).
% 2.10/0.65  fof(f48,plain,(
% 2.10/0.65    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 2.10/0.65    inference(cnf_transformation,[],[f36])).
% 2.10/0.65  fof(f58,plain,(
% 2.10/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f4])).
% 2.10/0.65  fof(f4,axiom,(
% 2.10/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.10/0.65  fof(f588,plain,(
% 2.10/0.65    ( ! [X4,X2,X3] : (r1_tarski(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4))) )),
% 2.10/0.65    inference(resolution,[],[f73,f54])).
% 2.10/0.65  fof(f54,plain,(
% 2.10/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f8])).
% 2.10/0.65  fof(f8,axiom,(
% 2.10/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.10/0.65  fof(f73,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f30])).
% 2.10/0.65  fof(f30,plain,(
% 2.10/0.65    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 2.10/0.65    inference(ennf_transformation,[],[f7])).
% 2.10/0.65  fof(f7,axiom,(
% 2.10/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).
% 2.10/0.65  fof(f618,plain,(
% 2.10/0.65    ~r1_tarski(sK1,sK2) | ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 2.10/0.65    inference(backward_demodulation,[],[f617,f611])).
% 2.10/0.65  fof(f617,plain,(
% 2.10/0.65    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 2.10/0.65    inference(backward_demodulation,[],[f49,f610])).
% 2.10/0.65  fof(f49,plain,(
% 2.10/0.65    ~r1_tarski(sK1,sK2) | ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 2.10/0.65    inference(cnf_transformation,[],[f36])).
% 2.10/0.65  fof(f2223,plain,(
% 2.10/0.65    r1_tarski(sK1,sK2)),
% 2.10/0.65    inference(backward_demodulation,[],[f783,f2217])).
% 2.10/0.65  fof(f2217,plain,(
% 2.10/0.65    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.10/0.65    inference(superposition,[],[f612,f766])).
% 2.10/0.65  fof(f766,plain,(
% 2.10/0.65    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 2.10/0.65    inference(forward_demodulation,[],[f761,f611])).
% 2.10/0.65  fof(f761,plain,(
% 2.10/0.65    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 2.10/0.65    inference(resolution,[],[f67,f47])).
% 2.10/0.65  fof(f67,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.10/0.65    inference(cnf_transformation,[],[f28])).
% 2.10/0.65  fof(f28,plain,(
% 2.10/0.65    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.65    inference(ennf_transformation,[],[f17])).
% 2.10/0.65  fof(f17,axiom,(
% 2.10/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.10/0.65  fof(f612,plain,(
% 2.10/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))) )),
% 2.10/0.65    inference(resolution,[],[f66,f78])).
% 2.10/0.65  fof(f78,plain,(
% 2.10/0.65    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 2.10/0.65    inference(backward_demodulation,[],[f55,f56])).
% 2.10/0.65  fof(f56,plain,(
% 2.10/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f18])).
% 2.10/0.65  fof(f18,axiom,(
% 2.10/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.10/0.65  fof(f55,plain,(
% 2.10/0.65    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f15])).
% 2.10/0.65  fof(f15,axiom,(
% 2.10/0.65    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.10/0.65  fof(f783,plain,(
% 2.10/0.65    r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 2.10/0.65    inference(superposition,[],[f592,f779])).
% 2.10/0.65  fof(f779,plain,(
% 2.10/0.65    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.10/0.65    inference(forward_demodulation,[],[f778,f183])).
% 2.10/0.65  fof(f778,plain,(
% 2.10/0.65    k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k5_xboole_0(sK1,k1_xboole_0)),
% 2.10/0.65    inference(superposition,[],[f58,f774])).
% 2.10/0.65  fof(f774,plain,(
% 2.10/0.65    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.10/0.65    inference(resolution,[],[f752,f53])).
% 2.10/0.65  fof(f752,plain,(
% 2.10/0.65    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) )),
% 2.10/0.65    inference(resolution,[],[f748,f64])).
% 2.10/0.65  fof(f748,plain,(
% 2.10/0.65    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.10/0.65    inference(subsumption_resolution,[],[f744,f72])).
% 2.10/0.65  fof(f744,plain,(
% 2.10/0.65    r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.10/0.65    inference(resolution,[],[f619,f255])).
% 2.10/0.65  fof(f255,plain,(
% 2.10/0.65    ( ! [X19,X20,X18] : (~r1_tarski(X20,k4_xboole_0(X19,X18)) | r1_xboole_0(X18,X20)) )),
% 2.10/0.65    inference(superposition,[],[f99,f240])).
% 2.10/0.65  fof(f240,plain,(
% 2.10/0.65    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1) )),
% 2.10/0.65    inference(forward_demodulation,[],[f239,f183])).
% 2.10/0.65  fof(f239,plain,(
% 2.10/0.65    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 2.10/0.65    inference(superposition,[],[f58,f223])).
% 2.10/0.65  fof(f223,plain,(
% 2.10/0.65    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.10/0.65    inference(resolution,[],[f207,f53])).
% 2.10/0.65  fof(f207,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 2.10/0.65    inference(resolution,[],[f199,f64])).
% 2.10/0.65  fof(f199,plain,(
% 2.10/0.65    ( ! [X19,X18] : (r1_xboole_0(X19,k4_xboole_0(X18,X19))) )),
% 2.10/0.65    inference(superposition,[],[f172,f187])).
% 2.10/0.65  fof(f187,plain,(
% 2.10/0.65    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.10/0.65    inference(forward_demodulation,[],[f185,f183])).
% 2.10/0.65  fof(f185,plain,(
% 2.10/0.65    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0)) )),
% 2.10/0.65    inference(superposition,[],[f58,f166])).
% 2.10/0.65  fof(f166,plain,(
% 2.10/0.65    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.10/0.65    inference(resolution,[],[f158,f53])).
% 2.10/0.65  fof(f158,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 2.10/0.65    inference(resolution,[],[f157,f64])).
% 2.10/0.65  fof(f157,plain,(
% 2.10/0.65    ( ! [X2] : (r1_xboole_0(X2,k1_xboole_0)) )),
% 2.10/0.65    inference(resolution,[],[f150,f65])).
% 2.10/0.65  fof(f150,plain,(
% 2.10/0.65    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.10/0.65    inference(resolution,[],[f149,f79])).
% 2.10/0.65  fof(f79,plain,(
% 2.10/0.65    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 2.10/0.65    inference(superposition,[],[f54,f51])).
% 2.10/0.65  fof(f149,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | r1_xboole_0(X1,X0)) )),
% 2.10/0.65    inference(superposition,[],[f75,f51])).
% 2.10/0.65  fof(f172,plain,(
% 2.10/0.65    ( ! [X6,X4,X5] : (r1_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,X4),X6))) )),
% 2.10/0.65    inference(resolution,[],[f147,f65])).
% 2.10/0.65  fof(f147,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1)) )),
% 2.10/0.65    inference(resolution,[],[f75,f54])).
% 2.10/0.65  fof(f592,plain,(
% 2.10/0.65    ( ! [X15] : (r1_tarski(k4_xboole_0(sK1,X15),k4_xboole_0(sK0,X15))) )),
% 2.10/0.65    inference(resolution,[],[f73,f91])).
% 2.10/0.65  fof(f91,plain,(
% 2.10/0.65    r1_tarski(sK1,sK0)),
% 2.10/0.65    inference(resolution,[],[f87,f77])).
% 2.10/0.65  fof(f77,plain,(
% 2.10/0.65    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 2.10/0.65    inference(equality_resolution,[],[f68])).
% 2.10/0.65  fof(f68,plain,(
% 2.10/0.65    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.10/0.65    inference(cnf_transformation,[],[f45])).
% 2.10/0.65  fof(f45,plain,(
% 2.10/0.65    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.10/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).
% 2.10/0.65  fof(f44,plain,(
% 2.10/0.65    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 2.10/0.65    introduced(choice_axiom,[])).
% 2.10/0.65  fof(f43,plain,(
% 2.10/0.65    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.10/0.65    inference(rectify,[],[f42])).
% 2.10/0.65  fof(f42,plain,(
% 2.10/0.65    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.10/0.65    inference(nnf_transformation,[],[f12])).
% 2.10/0.65  fof(f12,axiom,(
% 2.10/0.65    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.10/0.65  fof(f87,plain,(
% 2.10/0.65    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.10/0.65    inference(subsumption_resolution,[],[f83,f50])).
% 2.10/0.65  fof(f50,plain,(
% 2.10/0.65    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f16])).
% 2.10/0.65  fof(f16,axiom,(
% 2.10/0.65    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.10/0.65  fof(f83,plain,(
% 2.10/0.65    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.10/0.65    inference(resolution,[],[f59,f46])).
% 2.10/0.65  fof(f59,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f39])).
% 2.10/0.65  fof(f39,plain,(
% 2.10/0.65    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.10/0.65    inference(nnf_transformation,[],[f24])).
% 2.10/0.65  fof(f24,plain,(
% 2.10/0.65    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.10/0.65    inference(ennf_transformation,[],[f13])).
% 2.10/0.65  fof(f13,axiom,(
% 2.10/0.65    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.10/0.65  % SZS output end Proof for theBenchmark
% 2.10/0.65  % (13843)------------------------------
% 2.10/0.65  % (13843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.65  % (13843)Termination reason: Refutation
% 2.10/0.65  
% 2.10/0.65  % (13843)Memory used [KB]: 7803
% 2.10/0.65  % (13843)Time elapsed: 0.229 s
% 2.10/0.65  % (13843)------------------------------
% 2.10/0.65  % (13843)------------------------------
% 2.10/0.65  % (13832)Success in time 0.301 s
%------------------------------------------------------------------------------
