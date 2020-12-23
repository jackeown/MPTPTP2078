%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:38 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 439 expanded)
%              Number of leaves         :   20 ( 125 expanded)
%              Depth                    :   19
%              Number of atoms          :  175 ( 940 expanded)
%              Number of equality atoms :   84 ( 386 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f559,plain,(
    $false ),
    inference(subsumption_resolution,[],[f558,f256])).

fof(f256,plain,(
    ! [X2,X1] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f169,f84])).

fof(f84,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f54,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f54,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f168,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1(X0,X1))
      | r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f164,f129])).

fof(f129,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f125,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f55,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f125,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f67,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f51,f49])).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X0),k3_subset_1(X0,X1))
      | r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f70,f83])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f558,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK0),sK0) ),
    inference(forward_demodulation,[],[f556,f522])).

fof(f522,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f521,f331])).

fof(f331,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f258,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f258,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f169,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f38])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f521,plain,
    ( r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(superposition,[],[f256,f392])).

fof(f392,plain,
    ( sK0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f271,f391])).

fof(f391,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f385,f208])).

fof(f208,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f204,f87])).

fof(f87,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f59,f53])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f204,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f62,f90])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f385,plain,(
    k5_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f62,f332])).

fof(f332,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f258,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f271,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1)
    | sK0 = sK1 ),
    inference(forward_demodulation,[],[f270,f261])).

fof(f261,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f91,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f60,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f270,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0)
    | sK0 = sK1 ),
    inference(forward_demodulation,[],[f266,f62])).

fof(f266,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | sK0 = sK1 ),
    inference(superposition,[],[f107,f133])).

fof(f133,plain,
    ( k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f94,f128])).

fof(f128,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f67,f44])).

fof(f94,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f65,f81])).

fof(f81,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f45,f49])).

fof(f45,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f107,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f63,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f556,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1) ),
    inference(trivial_inequality_removal,[],[f525])).

fof(f525,plain,
    ( sK0 != sK0
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f132,f522])).

fof(f132,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | sK0 != sK1 ),
    inference(backward_demodulation,[],[f82,f128])).

fof(f82,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK0 != sK1 ),
    inference(backward_demodulation,[],[f46,f49])).

fof(f46,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:26:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (881)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (880)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (907)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (899)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (878)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (884)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (889)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (888)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (887)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (906)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (882)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (907)Refutation not found, incomplete strategy% (907)------------------------------
% 0.21/0.53  % (907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (891)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (901)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (907)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (907)Memory used [KB]: 6268
% 0.21/0.53  % (907)Time elapsed: 0.116 s
% 0.21/0.53  % (907)------------------------------
% 0.21/0.53  % (907)------------------------------
% 0.21/0.53  % (875)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (876)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (895)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (876)Refutation not found, incomplete strategy% (876)------------------------------
% 0.21/0.54  % (876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (876)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (876)Memory used [KB]: 1663
% 0.21/0.54  % (876)Time elapsed: 0.124 s
% 0.21/0.54  % (876)------------------------------
% 0.21/0.54  % (876)------------------------------
% 0.21/0.54  % (877)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (897)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (883)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (896)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (888)Refutation not found, incomplete strategy% (888)------------------------------
% 0.21/0.55  % (888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (888)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (888)Memory used [KB]: 10746
% 0.21/0.55  % (888)Time elapsed: 0.119 s
% 0.21/0.55  % (888)------------------------------
% 0.21/0.55  % (888)------------------------------
% 0.21/0.55  % (894)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (906)Refutation not found, incomplete strategy% (906)------------------------------
% 0.21/0.55  % (906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (885)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.49/0.55  % (886)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.49/0.55  % (909)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.49/0.56  % (904)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.49/0.56  % (898)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.56  % (908)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.49/0.56  % (908)Refutation not found, incomplete strategy% (908)------------------------------
% 1.49/0.56  % (908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (908)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (908)Memory used [KB]: 10746
% 1.49/0.56  % (908)Time elapsed: 0.145 s
% 1.49/0.56  % (908)------------------------------
% 1.49/0.56  % (908)------------------------------
% 1.49/0.56  % (893)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.49/0.56  % (909)Refutation not found, incomplete strategy% (909)------------------------------
% 1.49/0.56  % (909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (893)Refutation not found, incomplete strategy% (893)------------------------------
% 1.49/0.56  % (893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (893)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (893)Memory used [KB]: 10618
% 1.49/0.56  % (893)Time elapsed: 0.156 s
% 1.49/0.56  % (893)------------------------------
% 1.49/0.56  % (893)------------------------------
% 1.49/0.56  % (909)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (909)Memory used [KB]: 1663
% 1.49/0.56  % (909)Time elapsed: 0.156 s
% 1.49/0.56  % (909)------------------------------
% 1.49/0.56  % (909)------------------------------
% 1.49/0.56  % (890)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.49/0.56  % (906)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (906)Memory used [KB]: 6268
% 1.49/0.56  % (906)Time elapsed: 0.121 s
% 1.49/0.56  % (906)------------------------------
% 1.49/0.56  % (906)------------------------------
% 1.49/0.56  % (902)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.63/0.57  % (886)Refutation not found, incomplete strategy% (886)------------------------------
% 1.63/0.57  % (886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (886)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (886)Memory used [KB]: 10746
% 1.63/0.58  % (886)Time elapsed: 0.158 s
% 1.63/0.58  % (886)------------------------------
% 1.63/0.58  % (886)------------------------------
% 1.63/0.58  % (883)Refutation found. Thanks to Tanya!
% 1.63/0.58  % SZS status Theorem for theBenchmark
% 1.63/0.58  % SZS output start Proof for theBenchmark
% 1.63/0.58  fof(f559,plain,(
% 1.63/0.58    $false),
% 1.63/0.58    inference(subsumption_resolution,[],[f558,f256])).
% 1.63/0.58  fof(f256,plain,(
% 1.63/0.58    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(X1,X2),X1)) )),
% 1.63/0.58    inference(resolution,[],[f169,f84])).
% 1.63/0.58  fof(f84,plain,(
% 1.63/0.58    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 1.63/0.58    inference(forward_demodulation,[],[f54,f57])).
% 1.63/0.58  fof(f57,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f23])).
% 1.63/0.58  fof(f23,axiom,(
% 1.63/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.63/0.58  fof(f54,plain,(
% 1.63/0.58    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f21])).
% 1.63/0.58  fof(f21,axiom,(
% 1.63/0.58    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.63/0.58  fof(f169,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f168,f47])).
% 1.63/0.58  fof(f47,plain,(
% 1.63/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f8])).
% 1.63/0.58  fof(f8,axiom,(
% 1.63/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.63/0.58  fof(f168,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k3_subset_1(X0,X1)) | r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.63/0.58    inference(forward_demodulation,[],[f164,f129])).
% 1.63/0.58  fof(f129,plain,(
% 1.63/0.58    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.63/0.58    inference(forward_demodulation,[],[f125,f90])).
% 1.63/0.58  fof(f90,plain,(
% 1.63/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.63/0.58    inference(superposition,[],[f55,f59])).
% 1.63/0.58  fof(f59,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.63/0.58    inference(cnf_transformation,[],[f6])).
% 1.63/0.58  fof(f6,axiom,(
% 1.63/0.58    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.63/0.58  fof(f55,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f9])).
% 1.63/0.58  fof(f9,axiom,(
% 1.63/0.58    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.63/0.58  fof(f125,plain,(
% 1.63/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 1.63/0.58    inference(resolution,[],[f67,f83])).
% 1.63/0.58  fof(f83,plain,(
% 1.63/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.63/0.58    inference(forward_demodulation,[],[f51,f49])).
% 1.63/0.58  fof(f49,plain,(
% 1.63/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.63/0.58    inference(cnf_transformation,[],[f18])).
% 1.63/0.58  fof(f18,axiom,(
% 1.63/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.63/0.58  fof(f51,plain,(
% 1.63/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f20])).
% 1.63/0.58  fof(f20,axiom,(
% 1.63/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.63/0.58  fof(f67,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f33])).
% 1.63/0.58  fof(f33,plain,(
% 1.63/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f19])).
% 1.63/0.58  fof(f19,axiom,(
% 1.63/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.63/0.58  fof(f164,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r1_tarski(k3_subset_1(X0,X0),k3_subset_1(X0,X1)) | r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.63/0.58    inference(resolution,[],[f70,f83])).
% 1.63/0.58  fof(f70,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f40])).
% 1.63/0.58  fof(f40,plain,(
% 1.63/0.58    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.63/0.58    inference(nnf_transformation,[],[f35])).
% 1.63/0.58  fof(f35,plain,(
% 1.63/0.58    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f25])).
% 1.63/0.58  fof(f25,axiom,(
% 1.63/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 1.63/0.58  fof(f558,plain,(
% 1.63/0.58    ~r1_tarski(k4_xboole_0(sK0,sK0),sK0)),
% 1.63/0.58    inference(forward_demodulation,[],[f556,f522])).
% 1.63/0.59  fof(f522,plain,(
% 1.63/0.59    sK0 = sK1),
% 1.63/0.59    inference(subsumption_resolution,[],[f521,f331])).
% 1.63/0.59  fof(f331,plain,(
% 1.63/0.59    sK0 = sK1 | ~r1_tarski(sK0,sK1)),
% 1.63/0.59    inference(resolution,[],[f258,f73])).
% 1.63/0.59  fof(f73,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f42])).
% 1.63/0.59  fof(f42,plain,(
% 1.63/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.63/0.59    inference(flattening,[],[f41])).
% 1.63/0.59  fof(f41,plain,(
% 1.63/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.63/0.59    inference(nnf_transformation,[],[f3])).
% 1.63/0.59  fof(f3,axiom,(
% 1.63/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.63/0.59  fof(f258,plain,(
% 1.63/0.59    r1_tarski(sK1,sK0)),
% 1.63/0.59    inference(resolution,[],[f169,f44])).
% 1.63/0.59  fof(f44,plain,(
% 1.63/0.59    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.63/0.59    inference(cnf_transformation,[],[f39])).
% 1.63/0.59  fof(f39,plain,(
% 1.63/0.59    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f38])).
% 1.63/0.59  fof(f38,plain,(
% 1.63/0.59    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f37,plain,(
% 1.63/0.59    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.63/0.59    inference(flattening,[],[f36])).
% 1.63/0.59  fof(f36,plain,(
% 1.63/0.59    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.63/0.59    inference(nnf_transformation,[],[f30])).
% 1.63/0.59  fof(f30,plain,(
% 1.63/0.59    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f28])).
% 1.63/0.59  fof(f28,negated_conjecture,(
% 1.63/0.59    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.63/0.59    inference(negated_conjecture,[],[f27])).
% 1.63/0.59  fof(f27,conjecture,(
% 1.63/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 1.63/0.59  fof(f521,plain,(
% 1.63/0.59    r1_tarski(sK0,sK1) | sK0 = sK1),
% 1.63/0.59    inference(superposition,[],[f256,f392])).
% 1.63/0.59  fof(f392,plain,(
% 1.63/0.59    sK0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | sK0 = sK1),
% 1.63/0.59    inference(backward_demodulation,[],[f271,f391])).
% 1.63/0.59  fof(f391,plain,(
% 1.63/0.59    sK0 = k2_xboole_0(sK0,sK1)),
% 1.63/0.59    inference(forward_demodulation,[],[f385,f208])).
% 1.63/0.59  fof(f208,plain,(
% 1.63/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.63/0.59    inference(forward_demodulation,[],[f204,f87])).
% 1.63/0.59  fof(f87,plain,(
% 1.63/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.63/0.59    inference(superposition,[],[f59,f53])).
% 1.63/0.59  fof(f53,plain,(
% 1.63/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.63/0.59    inference(cnf_transformation,[],[f29])).
% 1.63/0.59  fof(f29,plain,(
% 1.63/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.63/0.59    inference(rectify,[],[f2])).
% 1.63/0.59  fof(f2,axiom,(
% 1.63/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.63/0.59  fof(f204,plain,(
% 1.63/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 1.63/0.59    inference(superposition,[],[f62,f90])).
% 1.63/0.59  fof(f62,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f10])).
% 1.63/0.59  fof(f10,axiom,(
% 1.63/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.63/0.59  fof(f385,plain,(
% 1.63/0.59    k5_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK1)),
% 1.63/0.59    inference(superposition,[],[f62,f332])).
% 1.63/0.59  fof(f332,plain,(
% 1.63/0.59    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.63/0.59    inference(resolution,[],[f258,f75])).
% 1.63/0.59  fof(f75,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.63/0.59    inference(cnf_transformation,[],[f43])).
% 1.63/0.59  fof(f43,plain,(
% 1.63/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.63/0.59    inference(nnf_transformation,[],[f4])).
% 1.63/0.59  fof(f4,axiom,(
% 1.63/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.63/0.59  fof(f271,plain,(
% 1.63/0.59    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1) | sK0 = sK1),
% 1.63/0.59    inference(forward_demodulation,[],[f270,f261])).
% 1.63/0.59  fof(f261,plain,(
% 1.63/0.59    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.63/0.59    inference(superposition,[],[f91,f60])).
% 1.63/0.59  fof(f60,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f14])).
% 1.63/0.59  fof(f14,axiom,(
% 1.63/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.63/0.59  fof(f91,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.63/0.59    inference(superposition,[],[f60,f56])).
% 1.63/0.59  fof(f56,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f11])).
% 1.63/0.59  fof(f11,axiom,(
% 1.63/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.63/0.59  fof(f270,plain,(
% 1.63/0.59    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0) | sK0 = sK1),
% 1.63/0.59    inference(forward_demodulation,[],[f266,f62])).
% 1.63/0.59  fof(f266,plain,(
% 1.63/0.59    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | sK0 = sK1),
% 1.63/0.59    inference(superposition,[],[f107,f133])).
% 1.63/0.59  fof(f133,plain,(
% 1.63/0.59    k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK1) | sK0 = sK1),
% 1.63/0.59    inference(backward_demodulation,[],[f94,f128])).
% 1.63/0.59  fof(f128,plain,(
% 1.63/0.59    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.63/0.59    inference(resolution,[],[f67,f44])).
% 1.63/0.59  fof(f94,plain,(
% 1.63/0.59    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | sK0 = sK1),
% 1.63/0.59    inference(resolution,[],[f65,f81])).
% 1.63/0.59  fof(f81,plain,(
% 1.63/0.59    r1_tarski(k3_subset_1(sK0,sK1),sK1) | sK0 = sK1),
% 1.63/0.59    inference(backward_demodulation,[],[f45,f49])).
% 1.63/0.59  fof(f45,plain,(
% 1.63/0.59    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.63/0.59    inference(cnf_transformation,[],[f39])).
% 1.63/0.59  fof(f65,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f31,plain,(
% 1.63/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.63/0.59    inference(ennf_transformation,[],[f7])).
% 1.63/0.59  fof(f7,axiom,(
% 1.63/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.63/0.59  fof(f107,plain,(
% 1.63/0.59    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.63/0.59    inference(superposition,[],[f63,f58])).
% 1.63/0.59  fof(f58,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f1])).
% 1.63/0.59  fof(f1,axiom,(
% 1.63/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.63/0.59  fof(f63,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f5])).
% 1.63/0.59  fof(f5,axiom,(
% 1.63/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.63/0.59  fof(f556,plain,(
% 1.63/0.59    ~r1_tarski(k4_xboole_0(sK0,sK1),sK1)),
% 1.63/0.59    inference(trivial_inequality_removal,[],[f525])).
% 1.63/0.59  fof(f525,plain,(
% 1.63/0.59    sK0 != sK0 | ~r1_tarski(k4_xboole_0(sK0,sK1),sK1)),
% 1.63/0.59    inference(backward_demodulation,[],[f132,f522])).
% 1.63/0.59  fof(f132,plain,(
% 1.63/0.59    ~r1_tarski(k4_xboole_0(sK0,sK1),sK1) | sK0 != sK1),
% 1.63/0.59    inference(backward_demodulation,[],[f82,f128])).
% 1.63/0.59  fof(f82,plain,(
% 1.63/0.59    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | sK0 != sK1),
% 1.63/0.59    inference(backward_demodulation,[],[f46,f49])).
% 1.63/0.59  fof(f46,plain,(
% 1.63/0.59    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.63/0.59    inference(cnf_transformation,[],[f39])).
% 1.63/0.59  % SZS output end Proof for theBenchmark
% 1.63/0.59  % (883)------------------------------
% 1.63/0.59  % (883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (883)Termination reason: Refutation
% 1.63/0.59  
% 1.63/0.59  % (883)Memory used [KB]: 2046
% 1.63/0.59  % (883)Time elapsed: 0.139 s
% 1.63/0.59  % (883)------------------------------
% 1.63/0.59  % (883)------------------------------
% 1.63/0.59  % (871)Success in time 0.224 s
%------------------------------------------------------------------------------
