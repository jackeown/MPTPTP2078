%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:00 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 238 expanded)
%              Number of leaves         :   21 (  73 expanded)
%              Depth                    :   19
%              Number of atoms          :  205 ( 378 expanded)
%              Number of equality atoms :   93 ( 226 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1112,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1109,f115])).

fof(f115,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f75,f113])).

fof(f113,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f61,f40])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f75,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f41,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f41,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f1109,plain,(
    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f925,f1099])).

fof(f1099,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f1029,f146])).

fof(f146,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f117,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f117,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f84,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f84,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f83,f74])).

fof(f74,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f83,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f82,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f55,f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1029,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),X2) = X2 ),
    inference(backward_demodulation,[],[f246,f1008])).

fof(f1008,plain,(
    ! [X4,X3] : k5_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,k4_xboole_0(X3,X4))) = X3 ),
    inference(superposition,[],[f940,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f940,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f97,f936])).

fof(f936,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(backward_demodulation,[],[f337,f931])).

fof(f931,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = X1 ),
    inference(backward_demodulation,[],[f237,f926])).

fof(f926,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f914,f98])).

fof(f98,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f95,f87])).

fof(f87,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f59,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f95,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f53,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f46,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f914,plain,(
    ! [X2,X3] : k3_xboole_0(X3,k3_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X2,X3),k1_xboole_0) ),
    inference(backward_demodulation,[],[f329,f909])).

fof(f909,plain,(
    ! [X8,X7] : k1_xboole_0 = k3_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f905,f78])).

fof(f905,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X7) = k3_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(superposition,[],[f53,f331])).

fof(f331,plain,(
    ! [X4,X5] : k4_xboole_0(X5,k4_xboole_0(X4,X5)) = X5 ),
    inference(forward_demodulation,[],[f330,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f48,f47])).

fof(f330,plain,(
    ! [X4,X5] : k2_xboole_0(X5,k3_xboole_0(X4,X5)) = k4_xboole_0(X5,k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f322,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f322,plain,(
    ! [X4,X5] : k2_xboole_0(X5,k3_xboole_0(X4,X5)) = k5_xboole_0(X5,k3_xboole_0(X5,k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f51,f127])).

fof(f127,plain,(
    ! [X4,X3] : k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(X4,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f126,f47])).

fof(f126,plain,(
    ! [X4,X3] : k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(k4_xboole_0(X3,X4),X4) ),
    inference(forward_demodulation,[],[f123,f52])).

fof(f123,plain,(
    ! [X4,X3] : k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X4) ),
    inference(superposition,[],[f69,f52])).

fof(f69,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f329,plain,(
    ! [X2,X3] : k4_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,k4_xboole_0(X2,X3))) = k3_xboole_0(X3,k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f321,f47])).

fof(f321,plain,(
    ! [X2,X3] : k3_xboole_0(k3_xboole_0(X2,X3),X3) = k4_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f53,f127])).

fof(f237,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X1))) = X1 ),
    inference(forward_demodulation,[],[f233,f76])).

fof(f233,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X2,X1)) = k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(superposition,[],[f54,f92])).

fof(f92,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f52,f47])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f337,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f97,f47])).

fof(f97,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f51,f53])).

fof(f246,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),X2) = k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f51,f96])).

fof(f96,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f53,f53])).

fof(f925,plain,(
    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f665,f924])).

fof(f924,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f910,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f910,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f104,f909])).

fof(f104,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f54,f51])).

fof(f665,plain,(
    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f135,f40])).

fof(f135,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(X0,k4_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f114,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f114,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f102,f113])).

fof(f102,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f60,f40])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:52:07 EST 2020
% 0.15/0.34  % CPUTime    : 
% 1.24/0.52  % (29763)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.52  % (29764)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.52  % (29788)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.41/0.54  % (29774)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.55  % (29790)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.41/0.57  % (29765)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.41/0.57  % (29776)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.57  % (29780)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.41/0.58  % (29784)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.41/0.58  % (29771)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.41/0.58  % (29791)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.41/0.58  % (29787)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.41/0.59  % (29781)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.59  % (29781)Refutation not found, incomplete strategy% (29781)------------------------------
% 1.41/0.59  % (29781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.59  % (29781)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.59  
% 1.41/0.59  % (29781)Memory used [KB]: 10618
% 1.41/0.59  % (29781)Time elapsed: 0.187 s
% 1.41/0.59  % (29781)------------------------------
% 1.41/0.59  % (29781)------------------------------
% 1.41/0.59  % (29792)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.41/0.60  % (29778)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.41/0.60  % (29785)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.60  % (29766)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.41/0.60  % (29767)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.41/0.61  % (29777)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.41/0.61  % (29769)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.61  % (29775)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.41/0.61  % (29775)Refutation not found, incomplete strategy% (29775)------------------------------
% 1.41/0.61  % (29775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.61  % (29775)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.61  
% 1.41/0.61  % (29775)Memory used [KB]: 10746
% 1.41/0.61  % (29775)Time elapsed: 0.205 s
% 1.41/0.61  % (29775)------------------------------
% 1.41/0.61  % (29775)------------------------------
% 1.41/0.62  % (29779)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.41/0.62  % (29783)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.41/0.62  % (29782)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.62  % (29789)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.63  % (29786)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.41/0.63  % (29772)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.11/0.63  % (29794)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 2.11/0.63  % (29794)Refutation not found, incomplete strategy% (29794)------------------------------
% 2.11/0.63  % (29794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.63  % (29794)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.63  
% 2.11/0.63  % (29794)Memory used [KB]: 1663
% 2.11/0.63  % (29794)Time elapsed: 0.002 s
% 2.11/0.63  % (29794)------------------------------
% 2.11/0.63  % (29794)------------------------------
% 2.11/0.64  % (29793)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.11/0.64  % (29771)Refutation found. Thanks to Tanya!
% 2.11/0.64  % SZS status Theorem for theBenchmark
% 2.11/0.64  % SZS output start Proof for theBenchmark
% 2.11/0.64  fof(f1112,plain,(
% 2.11/0.64    $false),
% 2.11/0.64    inference(subsumption_resolution,[],[f1109,f115])).
% 2.11/0.64  fof(f115,plain,(
% 2.11/0.64    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 2.11/0.64    inference(backward_demodulation,[],[f75,f113])).
% 2.11/0.64  fof(f113,plain,(
% 2.11/0.64    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.11/0.64    inference(resolution,[],[f61,f40])).
% 2.11/0.64  fof(f40,plain,(
% 2.11/0.64    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.11/0.64    inference(cnf_transformation,[],[f32])).
% 2.11/0.64  fof(f32,plain,(
% 2.11/0.64    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.11/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f31])).
% 2.11/0.64  fof(f31,plain,(
% 2.11/0.64    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.11/0.64    introduced(choice_axiom,[])).
% 2.11/0.64  fof(f24,plain,(
% 2.11/0.64    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.11/0.64    inference(ennf_transformation,[],[f23])).
% 2.11/0.64  fof(f23,negated_conjecture,(
% 2.11/0.64    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.11/0.64    inference(negated_conjecture,[],[f22])).
% 2.11/0.64  fof(f22,conjecture,(
% 2.11/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 2.11/0.64  fof(f61,plain,(
% 2.11/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f28])).
% 2.11/0.64  fof(f28,plain,(
% 2.11/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.11/0.64    inference(ennf_transformation,[],[f18])).
% 2.11/0.64  fof(f18,axiom,(
% 2.11/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.11/0.64  fof(f75,plain,(
% 2.11/0.64    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.11/0.64    inference(backward_demodulation,[],[f41,f44])).
% 2.11/0.64  fof(f44,plain,(
% 2.11/0.64    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.11/0.64    inference(cnf_transformation,[],[f17])).
% 2.11/0.64  fof(f17,axiom,(
% 2.11/0.64    ! [X0] : k2_subset_1(X0) = X0),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.11/0.64  fof(f41,plain,(
% 2.11/0.64    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.11/0.64    inference(cnf_transformation,[],[f32])).
% 2.11/0.64  fof(f1109,plain,(
% 2.11/0.64    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 2.11/0.64    inference(backward_demodulation,[],[f925,f1099])).
% 2.11/0.64  fof(f1099,plain,(
% 2.11/0.64    sK0 = k2_xboole_0(sK1,sK0)),
% 2.11/0.64    inference(superposition,[],[f1029,f146])).
% 2.11/0.64  fof(f146,plain,(
% 2.11/0.64    sK1 = k3_xboole_0(sK0,sK1)),
% 2.11/0.64    inference(superposition,[],[f117,f47])).
% 2.11/0.64  fof(f47,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f1])).
% 2.11/0.64  fof(f1,axiom,(
% 2.11/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.11/0.64  fof(f117,plain,(
% 2.11/0.64    sK1 = k3_xboole_0(sK1,sK0)),
% 2.11/0.64    inference(resolution,[],[f84,f59])).
% 2.11/0.64  fof(f59,plain,(
% 2.11/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.11/0.64    inference(cnf_transformation,[],[f26])).
% 2.11/0.64  fof(f26,plain,(
% 2.11/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.11/0.64    inference(ennf_transformation,[],[f6])).
% 2.11/0.64  fof(f6,axiom,(
% 2.11/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.11/0.64  fof(f84,plain,(
% 2.11/0.64    r1_tarski(sK1,sK0)),
% 2.11/0.64    inference(resolution,[],[f83,f74])).
% 2.11/0.64  fof(f74,plain,(
% 2.11/0.64    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 2.11/0.64    inference(equality_resolution,[],[f65])).
% 2.11/0.64  fof(f65,plain,(
% 2.11/0.64    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.11/0.64    inference(cnf_transformation,[],[f39])).
% 2.11/0.64  fof(f39,plain,(
% 2.11/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.11/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 2.11/0.64  fof(f38,plain,(
% 2.11/0.64    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 2.11/0.64    introduced(choice_axiom,[])).
% 2.11/0.64  fof(f37,plain,(
% 2.11/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.11/0.64    inference(rectify,[],[f36])).
% 2.11/0.64  fof(f36,plain,(
% 2.11/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.11/0.64    inference(nnf_transformation,[],[f14])).
% 2.11/0.64  fof(f14,axiom,(
% 2.11/0.64    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.11/0.64  fof(f83,plain,(
% 2.11/0.64    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.11/0.64    inference(subsumption_resolution,[],[f82,f42])).
% 2.11/0.64  fof(f42,plain,(
% 2.11/0.64    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.11/0.64    inference(cnf_transformation,[],[f20])).
% 2.11/0.64  fof(f20,axiom,(
% 2.11/0.64    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.11/0.64  fof(f82,plain,(
% 2.11/0.64    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.11/0.64    inference(resolution,[],[f55,f40])).
% 2.11/0.64  fof(f55,plain,(
% 2.11/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f33])).
% 2.11/0.64  fof(f33,plain,(
% 2.11/0.64    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.11/0.64    inference(nnf_transformation,[],[f25])).
% 2.11/0.64  fof(f25,plain,(
% 2.11/0.64    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.11/0.64    inference(ennf_transformation,[],[f16])).
% 2.11/0.64  fof(f16,axiom,(
% 2.11/0.64    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.11/0.64  fof(f1029,plain,(
% 2.11/0.64    ( ! [X2,X3] : (k2_xboole_0(k3_xboole_0(X2,X3),X2) = X2) )),
% 2.11/0.64    inference(backward_demodulation,[],[f246,f1008])).
% 2.11/0.64  fof(f1008,plain,(
% 2.11/0.64    ( ! [X4,X3] : (k5_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,k4_xboole_0(X3,X4))) = X3) )),
% 2.11/0.64    inference(superposition,[],[f940,f53])).
% 2.11/0.64  fof(f53,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.11/0.64    inference(cnf_transformation,[],[f9])).
% 2.11/0.64  fof(f9,axiom,(
% 2.11/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.11/0.64  fof(f940,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 2.11/0.64    inference(backward_demodulation,[],[f97,f936])).
% 2.11/0.64  fof(f936,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 2.11/0.64    inference(backward_demodulation,[],[f337,f931])).
% 2.11/0.64  fof(f931,plain,(
% 2.11/0.64    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = X1) )),
% 2.11/0.64    inference(backward_demodulation,[],[f237,f926])).
% 2.11/0.64  fof(f926,plain,(
% 2.11/0.64    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(X2,X3))) )),
% 2.11/0.64    inference(forward_demodulation,[],[f914,f98])).
% 2.11/0.64  fof(f98,plain,(
% 2.11/0.64    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.11/0.64    inference(forward_demodulation,[],[f95,f87])).
% 2.11/0.64  fof(f87,plain,(
% 2.11/0.64    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 2.11/0.64    inference(resolution,[],[f59,f71])).
% 2.11/0.64  fof(f71,plain,(
% 2.11/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.11/0.64    inference(equality_resolution,[],[f63])).
% 2.11/0.64  fof(f63,plain,(
% 2.11/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.11/0.64    inference(cnf_transformation,[],[f35])).
% 2.11/0.64  fof(f35,plain,(
% 2.11/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/0.64    inference(flattening,[],[f34])).
% 2.11/0.64  fof(f34,plain,(
% 2.11/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/0.64    inference(nnf_transformation,[],[f2])).
% 2.11/0.64  fof(f2,axiom,(
% 2.11/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.11/0.64  fof(f95,plain,(
% 2.11/0.64    ( ! [X2] : (k3_xboole_0(X2,X2) = k4_xboole_0(X2,k1_xboole_0)) )),
% 2.11/0.64    inference(superposition,[],[f53,f78])).
% 2.11/0.64  fof(f78,plain,(
% 2.11/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.11/0.64    inference(superposition,[],[f46,f48])).
% 2.11/0.64  fof(f48,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.11/0.64    inference(cnf_transformation,[],[f5])).
% 2.11/0.64  fof(f5,axiom,(
% 2.11/0.64    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.11/0.64  fof(f46,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.11/0.64    inference(cnf_transformation,[],[f8])).
% 2.11/0.64  fof(f8,axiom,(
% 2.11/0.64    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.11/0.64  fof(f914,plain,(
% 2.11/0.64    ( ! [X2,X3] : (k3_xboole_0(X3,k3_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X2,X3),k1_xboole_0)) )),
% 2.11/0.64    inference(backward_demodulation,[],[f329,f909])).
% 2.11/0.64  fof(f909,plain,(
% 2.11/0.64    ( ! [X8,X7] : (k1_xboole_0 = k3_xboole_0(X7,k4_xboole_0(X8,X7))) )),
% 2.11/0.64    inference(forward_demodulation,[],[f905,f78])).
% 2.11/0.64  fof(f905,plain,(
% 2.11/0.64    ( ! [X8,X7] : (k4_xboole_0(X7,X7) = k3_xboole_0(X7,k4_xboole_0(X8,X7))) )),
% 2.11/0.64    inference(superposition,[],[f53,f331])).
% 2.11/0.64  fof(f331,plain,(
% 2.11/0.64    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X4,X5)) = X5) )),
% 2.11/0.64    inference(forward_demodulation,[],[f330,f76])).
% 2.11/0.64  fof(f76,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 2.11/0.64    inference(superposition,[],[f48,f47])).
% 2.11/0.64  fof(f330,plain,(
% 2.11/0.64    ( ! [X4,X5] : (k2_xboole_0(X5,k3_xboole_0(X4,X5)) = k4_xboole_0(X5,k4_xboole_0(X4,X5))) )),
% 2.11/0.64    inference(forward_demodulation,[],[f322,f52])).
% 2.11/0.64  fof(f52,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.11/0.64    inference(cnf_transformation,[],[f3])).
% 2.11/0.64  fof(f3,axiom,(
% 2.11/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.11/0.64  fof(f322,plain,(
% 2.11/0.64    ( ! [X4,X5] : (k2_xboole_0(X5,k3_xboole_0(X4,X5)) = k5_xboole_0(X5,k3_xboole_0(X5,k4_xboole_0(X4,X5)))) )),
% 2.11/0.64    inference(superposition,[],[f51,f127])).
% 2.11/0.64  fof(f127,plain,(
% 2.11/0.64    ( ! [X4,X3] : (k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(X4,k4_xboole_0(X3,X4))) )),
% 2.11/0.64    inference(forward_demodulation,[],[f126,f47])).
% 2.11/0.64  fof(f126,plain,(
% 2.11/0.64    ( ! [X4,X3] : (k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(k4_xboole_0(X3,X4),X4)) )),
% 2.11/0.64    inference(forward_demodulation,[],[f123,f52])).
% 2.11/0.64  fof(f123,plain,(
% 2.11/0.64    ( ! [X4,X3] : (k4_xboole_0(k3_xboole_0(X3,X4),X4) = k3_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X4)) )),
% 2.11/0.64    inference(superposition,[],[f69,f52])).
% 2.11/0.64  fof(f69,plain,(
% 2.11/0.64    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.11/0.64    inference(cnf_transformation,[],[f4])).
% 2.11/0.64  fof(f4,axiom,(
% 2.11/0.64    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.11/0.64  fof(f51,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.11/0.64    inference(cnf_transformation,[],[f12])).
% 2.11/0.64  fof(f12,axiom,(
% 2.11/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.11/0.64  fof(f329,plain,(
% 2.11/0.64    ( ! [X2,X3] : (k4_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,k4_xboole_0(X2,X3))) = k3_xboole_0(X3,k3_xboole_0(X2,X3))) )),
% 2.11/0.64    inference(forward_demodulation,[],[f321,f47])).
% 2.11/0.64  fof(f321,plain,(
% 2.11/0.64    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(X2,X3),X3) = k4_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,k4_xboole_0(X2,X3)))) )),
% 2.11/0.64    inference(superposition,[],[f53,f127])).
% 2.11/0.64  fof(f237,plain,(
% 2.11/0.64    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X1))) = X1) )),
% 2.11/0.64    inference(forward_demodulation,[],[f233,f76])).
% 2.11/0.64  fof(f233,plain,(
% 2.11/0.64    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X2,X1)) = k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X1)))) )),
% 2.11/0.64    inference(superposition,[],[f54,f92])).
% 2.11/0.64  fof(f92,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 2.11/0.64    inference(superposition,[],[f52,f47])).
% 2.11/0.64  fof(f54,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.11/0.64    inference(cnf_transformation,[],[f11])).
% 2.11/0.64  fof(f11,axiom,(
% 2.11/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.11/0.64  fof(f337,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0))) )),
% 2.11/0.64    inference(superposition,[],[f97,f47])).
% 2.11/0.64  fof(f97,plain,(
% 2.11/0.64    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.11/0.64    inference(superposition,[],[f51,f53])).
% 2.11/0.64  fof(f246,plain,(
% 2.11/0.64    ( ! [X2,X3] : (k2_xboole_0(k3_xboole_0(X2,X3),X2) = k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 2.11/0.64    inference(superposition,[],[f51,f96])).
% 2.11/0.64  fof(f96,plain,(
% 2.11/0.64    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 2.11/0.64    inference(superposition,[],[f53,f53])).
% 2.11/0.64  fof(f925,plain,(
% 2.11/0.64    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0)),
% 2.11/0.64    inference(backward_demodulation,[],[f665,f924])).
% 2.11/0.64  fof(f924,plain,(
% 2.11/0.64    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 2.11/0.64    inference(forward_demodulation,[],[f910,f45])).
% 2.11/0.64  fof(f45,plain,(
% 2.11/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.11/0.64    inference(cnf_transformation,[],[f10])).
% 2.11/0.64  fof(f10,axiom,(
% 2.11/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.11/0.64  fof(f910,plain,(
% 2.11/0.64    ( ! [X2,X1] : (k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) )),
% 2.11/0.64    inference(backward_demodulation,[],[f104,f909])).
% 2.11/0.64  fof(f104,plain,(
% 2.11/0.64    ( ! [X2,X1] : (k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 2.11/0.64    inference(superposition,[],[f54,f51])).
% 2.11/0.64  fof(f665,plain,(
% 2.11/0.64    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 2.11/0.64    inference(resolution,[],[f135,f40])).
% 2.11/0.64  fof(f135,plain,(
% 2.11/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) )),
% 2.11/0.64    inference(resolution,[],[f114,f70])).
% 2.11/0.64  fof(f70,plain,(
% 2.11/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.11/0.64    inference(cnf_transformation,[],[f30])).
% 2.11/0.64  fof(f30,plain,(
% 2.11/0.64    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.11/0.64    inference(flattening,[],[f29])).
% 2.11/0.64  fof(f29,plain,(
% 2.11/0.64    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.11/0.64    inference(ennf_transformation,[],[f21])).
% 2.11/0.64  fof(f21,axiom,(
% 2.11/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.11/0.64  fof(f114,plain,(
% 2.11/0.64    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.11/0.64    inference(backward_demodulation,[],[f102,f113])).
% 2.11/0.64  fof(f102,plain,(
% 2.11/0.64    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.11/0.64    inference(resolution,[],[f60,f40])).
% 2.11/0.64  fof(f60,plain,(
% 2.11/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.11/0.64    inference(cnf_transformation,[],[f27])).
% 2.11/0.64  fof(f27,plain,(
% 2.11/0.64    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.11/0.64    inference(ennf_transformation,[],[f19])).
% 2.11/0.64  fof(f19,axiom,(
% 2.11/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.11/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.11/0.64  % SZS output end Proof for theBenchmark
% 2.11/0.64  % (29771)------------------------------
% 2.11/0.64  % (29771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.64  % (29771)Termination reason: Refutation
% 2.11/0.64  
% 2.11/0.64  % (29771)Memory used [KB]: 2558
% 2.11/0.64  % (29771)Time elapsed: 0.212 s
% 2.11/0.64  % (29771)------------------------------
% 2.11/0.64  % (29771)------------------------------
% 2.11/0.64  % (29793)Refutation not found, incomplete strategy% (29793)------------------------------
% 2.11/0.64  % (29793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.64  % (29793)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.64  
% 2.11/0.64  % (29793)Memory used [KB]: 10746
% 2.11/0.64  % (29793)Time elapsed: 0.213 s
% 2.11/0.64  % (29793)------------------------------
% 2.11/0.64  % (29793)------------------------------
% 2.11/0.65  % (29768)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 2.11/0.67  % (29756)Success in time 0.306 s
%------------------------------------------------------------------------------
