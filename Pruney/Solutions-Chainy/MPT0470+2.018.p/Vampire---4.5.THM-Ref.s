%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 238 expanded)
%              Number of leaves         :   18 (  65 expanded)
%              Depth                    :   20
%              Number of atoms          :  219 ( 498 expanded)
%              Number of equality atoms :   66 ( 208 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f660,plain,(
    $false ),
    inference(subsumption_resolution,[],[f659,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f659,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f643,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f643,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f642,f41])).

fof(f41,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f642,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f641])).

fof(f641,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f600])).

fof(f600,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f165,f575])).

fof(f575,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f556,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f63,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f556,plain,(
    ! [X0] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f551])).

fof(f551,plain,(
    ! [X0] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f411,f179])).

fof(f179,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f174,f84])).

fof(f174,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f168,f105])).

fof(f105,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f103,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f82,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f59,f56])).

fof(f56,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f103,plain,(
    ! [X4,X3] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(X3,X3),X4) ),
    inference(superposition,[],[f65,f83])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f168,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k1_xboole_0))))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f80,f45])).

fof(f45,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f80,plain,(
    ! [X0] :
      ( r1_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k4_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f77,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f77,plain,(
    ! [X0] :
      ( r1_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k4_relat_1(X0))))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f51,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f411,plain,(
    ! [X0] :
      ( r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),X0),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f409,f49])).

fof(f409,plain,(
    ! [X0] :
      ( r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),X0),k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f408])).

fof(f408,plain,(
    ! [X0] :
      ( r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),X0),k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f177,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(X0),X1)) = k5_relat_1(k4_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f137,f49])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(X0),X1)) = k5_relat_1(k4_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f55,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f177,plain,(
    ! [X1] :
      ( r1_tarski(k4_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f176,f105])).

fof(f176,plain,(
    ! [X1] :
      ( r1_tarski(k4_relat_1(k5_relat_1(X1,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(X1,k1_xboole_0)))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f170,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f170,plain,(
    ! [X1] :
      ( r1_tarski(k4_relat_1(k5_relat_1(X1,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(X1,k1_xboole_0)))))
      | ~ v1_relat_1(k5_relat_1(X1,k1_xboole_0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f80,f93])).

fof(f93,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f90,f84])).

fof(f90,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f54,f45])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f165,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f164,f41])).

fof(f164,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f151])).

fof(f151,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f42,f149])).

fof(f149,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f122,f84])).

fof(f122,plain,(
    ! [X4] :
      ( r1_tarski(k5_relat_1(X4,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f102,f121])).

fof(f121,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f120,f105])).

fof(f120,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_xboole_0,X1) = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f119,f83])).

fof(f119,plain,(
    ! [X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f111,f83])).

fof(f111,plain,(
    ! [X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[],[f66,f65])).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f102,plain,(
    ! [X4] :
      ( r1_tarski(k5_relat_1(X4,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X4,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f98,f60])).

fof(f98,plain,(
    ! [X4] :
      ( r1_tarski(k5_relat_1(X4,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X4,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(X4,k1_xboole_0))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f51,f93])).

fof(f42,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:17:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (15355)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (15363)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (15379)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (15359)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (15364)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.57  % (15356)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.57  % (15365)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.57  % (15365)Refutation not found, incomplete strategy% (15365)------------------------------
% 0.22/0.57  % (15365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (15365)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (15365)Memory used [KB]: 10618
% 0.22/0.57  % (15365)Time elapsed: 0.149 s
% 0.22/0.57  % (15365)------------------------------
% 0.22/0.57  % (15365)------------------------------
% 0.22/0.57  % (15361)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (15383)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.57  % (15383)Refutation not found, incomplete strategy% (15383)------------------------------
% 0.22/0.57  % (15383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (15358)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.57  % (15360)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.57  % (15367)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.58  % (15383)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (15383)Memory used [KB]: 10746
% 0.22/0.58  % (15383)Time elapsed: 0.153 s
% 0.22/0.58  % (15383)------------------------------
% 0.22/0.58  % (15383)------------------------------
% 0.22/0.59  % (15378)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.59  % (15357)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.59  % (15377)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.60  % (15382)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.60  % (15376)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.60  % (15375)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.60  % (15370)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.60  % (15369)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.61  % (15364)Refutation found. Thanks to Tanya!
% 0.22/0.61  % SZS status Theorem for theBenchmark
% 0.22/0.61  % SZS output start Proof for theBenchmark
% 0.22/0.61  fof(f660,plain,(
% 0.22/0.61    $false),
% 0.22/0.61    inference(subsumption_resolution,[],[f659,f43])).
% 0.22/0.61  fof(f43,plain,(
% 0.22/0.61    v1_xboole_0(k1_xboole_0)),
% 0.22/0.61    inference(cnf_transformation,[],[f1])).
% 0.22/0.61  fof(f1,axiom,(
% 0.22/0.61    v1_xboole_0(k1_xboole_0)),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.61  fof(f659,plain,(
% 0.22/0.61    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.61    inference(resolution,[],[f643,f48])).
% 0.22/0.61  fof(f48,plain,(
% 0.22/0.61    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f28])).
% 0.22/0.61  fof(f28,plain,(
% 0.22/0.61    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f15])).
% 0.22/0.61  fof(f15,axiom,(
% 0.22/0.61    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.61  fof(f643,plain,(
% 0.22/0.61    ~v1_relat_1(k1_xboole_0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f642,f41])).
% 0.22/0.61  fof(f41,plain,(
% 0.22/0.61    v1_relat_1(sK0)),
% 0.22/0.61    inference(cnf_transformation,[],[f38])).
% 0.22/0.61  fof(f38,plain,(
% 0.22/0.61    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.22/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f37])).
% 0.22/0.61  fof(f37,plain,(
% 0.22/0.61    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f27,plain,(
% 0.22/0.61    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f25])).
% 0.22/0.61  fof(f25,negated_conjecture,(
% 0.22/0.61    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.61    inference(negated_conjecture,[],[f24])).
% 0.22/0.61  fof(f24,conjecture,(
% 0.22/0.61    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.61  fof(f642,plain,(
% 0.22/0.61    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.22/0.61    inference(trivial_inequality_removal,[],[f641])).
% 0.22/0.61  fof(f641,plain,(
% 0.22/0.61    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.22/0.61    inference(duplicate_literal_removal,[],[f600])).
% 0.22/0.61  fof(f600,plain,(
% 0.22/0.61    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.61    inference(superposition,[],[f165,f575])).
% 0.22/0.61  fof(f575,plain,(
% 0.22/0.61    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.61    inference(resolution,[],[f556,f84])).
% 0.22/0.61  fof(f84,plain,(
% 0.22/0.61    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.61    inference(resolution,[],[f63,f46])).
% 0.22/0.61  fof(f46,plain,(
% 0.22/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f5])).
% 0.22/0.61  fof(f5,axiom,(
% 0.22/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.61  fof(f63,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f40])).
% 0.22/0.61  fof(f40,plain,(
% 0.22/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.61    inference(flattening,[],[f39])).
% 0.22/0.61  fof(f39,plain,(
% 0.22/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.61    inference(nnf_transformation,[],[f3])).
% 0.22/0.61  fof(f3,axiom,(
% 0.22/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.61  fof(f556,plain,(
% 0.22/0.61    ( ! [X0] : (r1_tarski(k5_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(duplicate_literal_removal,[],[f551])).
% 0.22/0.61  fof(f551,plain,(
% 0.22/0.61    ( ! [X0] : (r1_tarski(k5_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.61    inference(superposition,[],[f411,f179])).
% 0.22/0.61  fof(f179,plain,(
% 0.22/0.61    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.61    inference(resolution,[],[f174,f84])).
% 0.22/0.61  fof(f174,plain,(
% 0.22/0.61    r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.61    inference(forward_demodulation,[],[f168,f105])).
% 0.22/0.61  fof(f105,plain,(
% 0.22/0.61    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)) )),
% 0.22/0.61    inference(forward_demodulation,[],[f103,f83])).
% 0.22/0.61  fof(f83,plain,(
% 0.22/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.61    inference(forward_demodulation,[],[f82,f47])).
% 0.22/0.61  fof(f47,plain,(
% 0.22/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f6])).
% 0.22/0.61  fof(f6,axiom,(
% 0.22/0.61    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.61  fof(f82,plain,(
% 0.22/0.61    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.61    inference(superposition,[],[f59,f56])).
% 0.22/0.61  fof(f56,plain,(
% 0.22/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.61    inference(cnf_transformation,[],[f26])).
% 0.22/0.61  fof(f26,plain,(
% 0.22/0.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.61    inference(rectify,[],[f2])).
% 0.22/0.61  fof(f2,axiom,(
% 0.22/0.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.61  fof(f59,plain,(
% 0.22/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.61    inference(cnf_transformation,[],[f4])).
% 0.22/0.61  fof(f4,axiom,(
% 0.22/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.61  fof(f103,plain,(
% 0.22/0.61    ( ! [X4,X3] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(X3,X3),X4)) )),
% 0.22/0.61    inference(superposition,[],[f65,f83])).
% 0.22/0.61  fof(f65,plain,(
% 0.22/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.61    inference(cnf_transformation,[],[f13])).
% 0.22/0.61  fof(f13,axiom,(
% 0.22/0.61    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 0.22/0.61  fof(f168,plain,(
% 0.22/0.61    r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k1_xboole_0)))) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.61    inference(superposition,[],[f80,f45])).
% 0.22/0.61  fof(f45,plain,(
% 0.22/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.61    inference(cnf_transformation,[],[f23])).
% 0.22/0.61  fof(f23,axiom,(
% 0.22/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.61  fof(f80,plain,(
% 0.22/0.61    ( ! [X0] : (r1_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k4_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f77,f49])).
% 0.22/0.61  fof(f49,plain,(
% 0.22/0.61    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f29])).
% 0.22/0.61  fof(f29,plain,(
% 0.22/0.61    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f16])).
% 0.22/0.61  fof(f16,axiom,(
% 0.22/0.61    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.61  fof(f77,plain,(
% 0.22/0.61    ( ! [X0] : (r1_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k4_relat_1(X0)))) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(superposition,[],[f51,f52])).
% 0.22/0.61  fof(f52,plain,(
% 0.22/0.61    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f32])).
% 0.22/0.61  fof(f32,plain,(
% 0.22/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f20])).
% 0.22/0.61  fof(f20,axiom,(
% 0.22/0.61    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.61  fof(f51,plain,(
% 0.22/0.61    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f31])).
% 0.22/0.61  fof(f31,plain,(
% 0.22/0.61    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f19])).
% 0.22/0.61  fof(f19,axiom,(
% 0.22/0.61    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.61  fof(f411,plain,(
% 0.22/0.61    ( ! [X0] : (r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f409,f49])).
% 0.22/0.61  fof(f409,plain,(
% 0.22/0.61    ( ! [X0] : (r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),X0),k1_xboole_0) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(duplicate_literal_removal,[],[f408])).
% 0.22/0.61  fof(f408,plain,(
% 0.22/0.61    ( ! [X0] : (r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),X0),k1_xboole_0) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(superposition,[],[f177,f141])).
% 0.22/0.61  fof(f141,plain,(
% 0.22/0.61    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k4_relat_1(X0),X1)) = k5_relat_1(k4_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f137,f49])).
% 0.22/0.61  fof(f137,plain,(
% 0.22/0.61    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k4_relat_1(X0),X1)) = k5_relat_1(k4_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(superposition,[],[f55,f50])).
% 0.22/0.61  fof(f50,plain,(
% 0.22/0.61    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f30])).
% 0.22/0.61  fof(f30,plain,(
% 0.22/0.61    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f18])).
% 0.22/0.61  fof(f18,axiom,(
% 0.22/0.61    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.22/0.61  fof(f55,plain,(
% 0.22/0.61    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f34])).
% 0.22/0.61  fof(f34,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f22])).
% 0.22/0.61  fof(f22,axiom,(
% 0.22/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 0.22/0.61  fof(f177,plain,(
% 0.22/0.61    ( ! [X1] : (r1_tarski(k4_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X1) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.61    inference(forward_demodulation,[],[f176,f105])).
% 0.22/0.61  fof(f176,plain,(
% 0.22/0.61    ( ! [X1] : (r1_tarski(k4_relat_1(k5_relat_1(X1,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(X1,k1_xboole_0))))) | ~v1_relat_1(X1) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f170,f60])).
% 0.22/0.61  fof(f60,plain,(
% 0.22/0.61    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f36])).
% 0.22/0.61  fof(f36,plain,(
% 0.22/0.61    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.61    inference(flattening,[],[f35])).
% 0.22/0.61  fof(f35,plain,(
% 0.22/0.61    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f17])).
% 0.22/0.61  fof(f17,axiom,(
% 0.22/0.61    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.61  fof(f170,plain,(
% 0.22/0.61    ( ! [X1] : (r1_tarski(k4_relat_1(k5_relat_1(X1,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(X1,k1_xboole_0))))) | ~v1_relat_1(k5_relat_1(X1,k1_xboole_0)) | ~v1_relat_1(X1) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.61    inference(superposition,[],[f80,f93])).
% 0.22/0.61  fof(f93,plain,(
% 0.22/0.61    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.61    inference(resolution,[],[f90,f84])).
% 0.22/0.61  fof(f90,plain,(
% 0.22/0.61    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(superposition,[],[f54,f45])).
% 0.22/0.61  fof(f54,plain,(
% 0.22/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f33])).
% 0.22/0.61  fof(f33,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f21])).
% 0.22/0.61  fof(f21,axiom,(
% 0.22/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.22/0.61  fof(f165,plain,(
% 0.22/0.61    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f164,f41])).
% 0.22/0.61  fof(f164,plain,(
% 0.22/0.61    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.22/0.61    inference(trivial_inequality_removal,[],[f151])).
% 0.22/0.61  fof(f151,plain,(
% 0.22/0.61    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.22/0.61    inference(superposition,[],[f42,f149])).
% 0.22/0.61  fof(f149,plain,(
% 0.22/0.61    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.61    inference(resolution,[],[f122,f84])).
% 0.22/0.61  fof(f122,plain,(
% 0.22/0.61    ( ! [X4] : (r1_tarski(k5_relat_1(X4,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(X4) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.61    inference(backward_demodulation,[],[f102,f121])).
% 0.22/0.61  fof(f121,plain,(
% 0.22/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.61    inference(forward_demodulation,[],[f120,f105])).
% 0.22/0.61  fof(f120,plain,(
% 0.22/0.61    ( ! [X0,X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.61    inference(forward_demodulation,[],[f119,f83])).
% 0.22/0.61  fof(f119,plain,(
% 0.22/0.61    ( ! [X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.61    inference(forward_demodulation,[],[f111,f83])).
% 0.22/0.61  fof(f111,plain,(
% 0.22/0.61    ( ! [X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k4_xboole_0(X1,X1))) )),
% 0.22/0.61    inference(superposition,[],[f66,f65])).
% 0.22/0.61  fof(f66,plain,(
% 0.22/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.61    inference(cnf_transformation,[],[f13])).
% 0.22/0.61  fof(f102,plain,(
% 0.22/0.61    ( ! [X4] : (r1_tarski(k5_relat_1(X4,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X4,k1_xboole_0)),k1_xboole_0)) | ~v1_relat_1(X4) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f98,f60])).
% 0.22/0.61  fof(f98,plain,(
% 0.22/0.61    ( ! [X4] : (r1_tarski(k5_relat_1(X4,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X4,k1_xboole_0)),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(X4,k1_xboole_0)) | ~v1_relat_1(X4) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.61    inference(superposition,[],[f51,f93])).
% 0.22/0.61  fof(f42,plain,(
% 0.22/0.61    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.61    inference(cnf_transformation,[],[f38])).
% 0.22/0.61  % SZS output end Proof for theBenchmark
% 0.22/0.61  % (15364)------------------------------
% 0.22/0.61  % (15364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (15364)Termination reason: Refutation
% 0.22/0.61  
% 0.22/0.61  % (15364)Memory used [KB]: 2046
% 0.22/0.61  % (15364)Time elapsed: 0.188 s
% 0.22/0.61  % (15364)------------------------------
% 0.22/0.61  % (15364)------------------------------
% 0.22/0.61  % (15354)Success in time 0.245 s
%------------------------------------------------------------------------------
