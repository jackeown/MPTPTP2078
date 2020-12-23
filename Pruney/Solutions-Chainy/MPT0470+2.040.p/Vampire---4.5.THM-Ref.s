%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 155 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  187 ( 306 expanded)
%              Number of equality atoms :   71 ( 160 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f432,plain,(
    $false ),
    inference(subsumption_resolution,[],[f431,f41])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f431,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f404,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f404,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f403,f39])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f403,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f402])).

fof(f402,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f375])).

fof(f375,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f148,f366])).

fof(f366,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f365,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f365,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f364,f43])).

fof(f43,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f364,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f363,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f363,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k3_xboole_0(k5_relat_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f352,f90])).

fof(f90,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f88,f71])).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f70,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f70,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f55,f52])).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f88,plain,(
    ! [X4,X3] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(X3,X3),X4) ),
    inference(superposition,[],[f61,f71])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f352,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k3_xboole_0(k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0))))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f125,f42])).

fof(f42,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1))))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f124,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f124,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1))))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f48,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f48,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f148,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f147,f39])).

fof(f147,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f40,f135])).

fof(f135,plain,(
    ! [X4] :
      ( k1_xboole_0 = k5_relat_1(X4,k1_xboole_0)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f134,f45])).

fof(f134,plain,(
    ! [X4] :
      ( k5_relat_1(X4,k1_xboole_0) = k3_xboole_0(k5_relat_1(X4,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f133,f108])).

fof(f108,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f107,f90])).

fof(f107,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_xboole_0,X1) = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f106,f71])).

fof(f106,plain,(
    ! [X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f98,f71])).

fof(f98,plain,(
    ! [X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[],[f62,f61])).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f133,plain,(
    ! [X4] :
      ( k5_relat_1(X4,k1_xboole_0) = k3_xboole_0(k5_relat_1(X4,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X4,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f129,f56])).

fof(f129,plain,(
    ! [X4] :
      ( k5_relat_1(X4,k1_xboole_0) = k3_xboole_0(k5_relat_1(X4,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X4,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(X4,k1_xboole_0))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f48,f122])).

fof(f122,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f85,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f59,f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f85,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f49,f43])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f40,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:43:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (9013)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.49  % (9037)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.50  % (9015)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (9037)Refutation not found, incomplete strategy% (9037)------------------------------
% 0.22/0.51  % (9037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9037)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9037)Memory used [KB]: 10746
% 0.22/0.51  % (9037)Time elapsed: 0.121 s
% 0.22/0.51  % (9037)------------------------------
% 0.22/0.51  % (9037)------------------------------
% 0.22/0.52  % (9029)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (9022)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (9031)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (9032)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (9023)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (9024)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (9014)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (9012)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (9011)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (9038)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (9010)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (9036)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (9035)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (9018)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (9019)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (9030)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (9038)Refutation not found, incomplete strategy% (9038)------------------------------
% 0.22/0.55  % (9038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9038)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9038)Memory used [KB]: 1663
% 0.22/0.55  % (9038)Time elapsed: 0.003 s
% 0.22/0.55  % (9038)------------------------------
% 0.22/0.55  % (9038)------------------------------
% 0.22/0.55  % (9019)Refutation not found, incomplete strategy% (9019)------------------------------
% 0.22/0.55  % (9019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9019)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9019)Memory used [KB]: 10746
% 0.22/0.55  % (9019)Time elapsed: 0.141 s
% 0.22/0.55  % (9019)------------------------------
% 0.22/0.55  % (9019)------------------------------
% 0.22/0.55  % (9027)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (9028)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (9018)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (9034)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (9016)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.56  % (9021)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (9026)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (9033)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (9020)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (9017)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f432,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(subsumption_resolution,[],[f431,f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    v1_xboole_0(k1_xboole_0)),
% 0.22/0.58    inference(cnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    v1_xboole_0(k1_xboole_0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.58  fof(f431,plain,(
% 0.22/0.58    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.58    inference(resolution,[],[f404,f47])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,axiom,(
% 0.22/0.58    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.58  fof(f404,plain,(
% 0.22/0.58    ~v1_relat_1(k1_xboole_0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f403,f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    v1_relat_1(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,negated_conjecture,(
% 0.22/0.58    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.58    inference(negated_conjecture,[],[f23])).
% 0.22/0.58  fof(f23,conjecture,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.58  fof(f403,plain,(
% 0.22/0.58    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f402])).
% 0.22/0.58  fof(f402,plain,(
% 0.22/0.58    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f375])).
% 0.22/0.58  fof(f375,plain,(
% 0.22/0.58    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.58    inference(superposition,[],[f148,f366])).
% 0.22/0.58  fof(f366,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f365,f44])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.58  fof(f365,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f364,f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,axiom,(
% 0.22/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.58  fof(f364,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f363,f45])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.58  fof(f363,plain,(
% 0.22/0.58    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k3_xboole_0(k5_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f352,f90])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f88,f71])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f70,f46])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 0.22/0.58    inference(superposition,[],[f55,f52])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.58    inference(rectify,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.58  fof(f88,plain,(
% 0.22/0.58    ( ! [X4,X3] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(X3,X3),X4)) )),
% 0.22/0.58    inference(superposition,[],[f61,f71])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 0.22/0.58  fof(f352,plain,(
% 0.22/0.58    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k3_xboole_0(k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0)))) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.58    inference(superposition,[],[f125,f42])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f125,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1)))) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f124,f56])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(flattening,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f17])).
% 0.22/0.58  fof(f17,axiom,(
% 0.22/0.58    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.58  fof(f124,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1)))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(superposition,[],[f48,f50])).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(flattening,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,axiom,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,axiom,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 0.22/0.58  fof(f148,plain,(
% 0.22/0.58    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f147,f39])).
% 0.22/0.58  fof(f147,plain,(
% 0.22/0.58    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f136])).
% 0.22/0.58  fof(f136,plain,(
% 0.22/0.58    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.58    inference(superposition,[],[f40,f135])).
% 0.22/0.58  fof(f135,plain,(
% 0.22/0.58    ( ! [X4] : (k1_xboole_0 = k5_relat_1(X4,k1_xboole_0) | ~v1_relat_1(X4) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f134,f45])).
% 0.22/0.58  fof(f134,plain,(
% 0.22/0.58    ( ! [X4] : (k5_relat_1(X4,k1_xboole_0) = k3_xboole_0(k5_relat_1(X4,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(X4) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f133,f108])).
% 0.22/0.58  fof(f108,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f107,f90])).
% 0.22/0.58  fof(f107,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f106,f71])).
% 0.22/0.58  fof(f106,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f98,f71])).
% 0.22/0.58  fof(f98,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k4_xboole_0(X1,X1))) )),
% 0.22/0.58    inference(superposition,[],[f62,f61])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f133,plain,(
% 0.22/0.58    ( ! [X4] : (k5_relat_1(X4,k1_xboole_0) = k3_xboole_0(k5_relat_1(X4,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X4,k1_xboole_0)),k1_xboole_0)) | ~v1_relat_1(X4) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f129,f56])).
% 0.22/0.58  fof(f129,plain,(
% 0.22/0.58    ( ! [X4] : (k5_relat_1(X4,k1_xboole_0) = k3_xboole_0(k5_relat_1(X4,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X4,k1_xboole_0)),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(X4,k1_xboole_0)) | ~v1_relat_1(X4) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.58    inference(superposition,[],[f48,f122])).
% 0.22/0.58  fof(f122,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.58    inference(resolution,[],[f85,f72])).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(resolution,[],[f59,f44])).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.58    inference(flattening,[],[f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(superposition,[],[f49,f43])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,axiom,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (9018)------------------------------
% 0.22/0.58  % (9018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (9018)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (9018)Memory used [KB]: 2046
% 0.22/0.58  % (9018)Time elapsed: 0.140 s
% 0.22/0.58  % (9018)------------------------------
% 0.22/0.58  % (9018)------------------------------
% 0.22/0.58  % (9008)Success in time 0.216 s
%------------------------------------------------------------------------------
