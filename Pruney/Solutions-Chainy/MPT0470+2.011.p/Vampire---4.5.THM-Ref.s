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
% DateTime   : Thu Dec  3 12:47:45 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 227 expanded)
%              Number of leaves         :   17 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  175 ( 469 expanded)
%              Number of equality atoms :   66 ( 172 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f464,plain,(
    $false ),
    inference(subsumption_resolution,[],[f463,f206])).

fof(f206,plain,(
    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f42,f191])).

fof(f191,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f190,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f190,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f188,f134])).

fof(f134,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4) ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f75,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0)) ),
    inference(resolution,[],[f60,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f188,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) ),
    inference(backward_demodulation,[],[f157,f184])).

fof(f184,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f116,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f64,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f64,plain,(
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

fof(f116,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f114,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f114,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f103,f70])).

fof(f70,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,sK0)),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f157,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) ),
    inference(resolution,[],[f111,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f111,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f91,f70])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,sK0)) ) ),
    inference(resolution,[],[f61,f41])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f42,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f463,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f462,f47])).

fof(f462,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f455,f124])).

fof(f124,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(X4,k1_xboole_0) ),
    inference(resolution,[],[f74,f49])).

fof(f74,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f59,f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f455,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f348,f453])).

fof(f453,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f363,f94])).

fof(f363,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f344,f349])).

fof(f349,plain,(
    k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f318,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f318,plain,(
    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f92,f41])).

fof(f92,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f61,f70])).

fof(f344,plain,(
    r1_tarski(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f248,f336])).

fof(f336,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f285,f41])).

fof(f285,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X1)) ) ),
    inference(backward_demodulation,[],[f107,f280])).

fof(f280,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f279,f47])).

fof(f279,plain,(
    k4_relat_1(k1_xboole_0) = k3_xboole_0(k4_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f278,f124])).

fof(f278,plain,(
    k4_relat_1(k1_xboole_0) = k3_xboole_0(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f265,f83])).

fof(f83,plain,(
    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f82,f44])).

fof(f82,plain,(
    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f54,f70])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f265,plain,(
    k4_relat_1(k1_xboole_0) = k3_xboole_0(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k2_relat_1(k4_relat_1(k1_xboole_0)))) ),
    inference(resolution,[],[f73,f52])).

fof(f73,plain,(
    v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f50,f70])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f107,plain,(
    ! [X1] :
      ( k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f56,f70])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f248,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f242,f44])).

fof(f242,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f105,f70])).

fof(f105,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k1_relat_1(k5_relat_1(X2,k4_relat_1(sK0))),k1_relat_1(X2)) ) ),
    inference(resolution,[],[f55,f72])).

fof(f72,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f50,f41])).

fof(f348,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))) ),
    inference(resolution,[],[f318,f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:50:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (20256)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.46  % (20264)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.49  % (20248)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (20251)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (20255)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (20247)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (20262)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (20271)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (20254)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (20259)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (20269)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (20257)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (20263)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (20261)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (20249)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (20250)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (20266)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (20272)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (20275)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (20252)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (20260)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (20258)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (20273)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (20263)Refutation not found, incomplete strategy% (20263)------------------------------
% 0.20/0.53  % (20263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20263)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20263)Memory used [KB]: 10618
% 0.20/0.53  % (20263)Time elapsed: 0.126 s
% 0.20/0.53  % (20263)------------------------------
% 0.20/0.53  % (20263)------------------------------
% 0.20/0.53  % (20253)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (20270)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (20274)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (20267)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (20275)Refutation not found, incomplete strategy% (20275)------------------------------
% 0.20/0.54  % (20275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (20275)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (20275)Memory used [KB]: 10618
% 0.20/0.54  % (20275)Time elapsed: 0.130 s
% 0.20/0.54  % (20275)------------------------------
% 0.20/0.54  % (20275)------------------------------
% 0.20/0.54  % (20265)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (20276)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (20257)Refutation not found, incomplete strategy% (20257)------------------------------
% 0.20/0.55  % (20257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20257)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (20257)Memory used [KB]: 10618
% 0.20/0.55  % (20257)Time elapsed: 0.140 s
% 0.20/0.55  % (20257)------------------------------
% 0.20/0.55  % (20257)------------------------------
% 0.20/0.55  % (20276)Refutation not found, incomplete strategy% (20276)------------------------------
% 0.20/0.55  % (20276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20276)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (20276)Memory used [KB]: 1663
% 0.20/0.55  % (20276)Time elapsed: 0.139 s
% 0.20/0.55  % (20276)------------------------------
% 0.20/0.55  % (20276)------------------------------
% 0.20/0.55  % (20268)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.61/0.56  % (20254)Refutation found. Thanks to Tanya!
% 1.61/0.56  % SZS status Theorem for theBenchmark
% 1.61/0.57  % SZS output start Proof for theBenchmark
% 1.61/0.57  fof(f464,plain,(
% 1.61/0.57    $false),
% 1.61/0.57    inference(subsumption_resolution,[],[f463,f206])).
% 1.61/0.57  fof(f206,plain,(
% 1.61/0.57    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.61/0.57    inference(trivial_inequality_removal,[],[f192])).
% 1.61/0.57  fof(f192,plain,(
% 1.61/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.61/0.57    inference(backward_demodulation,[],[f42,f191])).
% 1.61/0.57  fof(f191,plain,(
% 1.61/0.57    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.61/0.57    inference(forward_demodulation,[],[f190,f47])).
% 1.61/0.57  fof(f47,plain,(
% 1.61/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f4])).
% 1.61/0.57  fof(f4,axiom,(
% 1.61/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.61/0.57  fof(f190,plain,(
% 1.61/0.57    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)),
% 1.61/0.57    inference(forward_demodulation,[],[f188,f134])).
% 1.61/0.57  fof(f134,plain,(
% 1.61/0.57    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)) )),
% 1.61/0.57    inference(resolution,[],[f75,f49])).
% 1.61/0.57  fof(f49,plain,(
% 1.61/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  fof(f26,plain,(
% 1.61/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f2])).
% 1.61/0.57  fof(f2,axiom,(
% 1.61/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.61/0.57  fof(f75,plain,(
% 1.61/0.57    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))) )),
% 1.61/0.57    inference(resolution,[],[f60,f43])).
% 1.61/0.57  fof(f43,plain,(
% 1.61/0.57    v1_xboole_0(k1_xboole_0)),
% 1.61/0.57    inference(cnf_transformation,[],[f1])).
% 1.61/0.57  fof(f1,axiom,(
% 1.61/0.57    v1_xboole_0(k1_xboole_0)),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.61/0.57  fof(f60,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f34])).
% 1.61/0.57  fof(f34,plain,(
% 1.61/0.57    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f11])).
% 1.61/0.57  fof(f11,axiom,(
% 1.61/0.57    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.61/0.57  fof(f188,plain,(
% 1.61/0.57    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))),
% 1.61/0.57    inference(backward_demodulation,[],[f157,f184])).
% 1.61/0.57  fof(f184,plain,(
% 1.61/0.57    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.61/0.57    inference(resolution,[],[f116,f94])).
% 1.61/0.57  fof(f94,plain,(
% 1.61/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.61/0.57    inference(resolution,[],[f64,f46])).
% 1.61/0.57  fof(f46,plain,(
% 1.61/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f5])).
% 1.61/0.57  fof(f5,axiom,(
% 1.61/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.61/0.57  fof(f64,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f40])).
% 1.61/0.57  fof(f40,plain,(
% 1.61/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.57    inference(flattening,[],[f39])).
% 1.61/0.57  fof(f39,plain,(
% 1.61/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.57    inference(nnf_transformation,[],[f3])).
% 1.61/0.57  fof(f3,axiom,(
% 1.61/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.61/0.57  fof(f116,plain,(
% 1.61/0.57    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)),
% 1.61/0.57    inference(forward_demodulation,[],[f114,f44])).
% 1.61/0.57  fof(f44,plain,(
% 1.61/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.61/0.57    inference(cnf_transformation,[],[f21])).
% 1.61/0.57  fof(f21,axiom,(
% 1.61/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.61/0.57  fof(f114,plain,(
% 1.61/0.57    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0))),
% 1.61/0.57    inference(resolution,[],[f103,f70])).
% 1.61/0.57  fof(f70,plain,(
% 1.61/0.57    v1_relat_1(k1_xboole_0)),
% 1.61/0.57    inference(resolution,[],[f48,f43])).
% 1.61/0.57  fof(f48,plain,(
% 1.61/0.57    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f25])).
% 1.61/0.57  fof(f25,plain,(
% 1.61/0.57    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f13])).
% 1.61/0.57  fof(f13,axiom,(
% 1.61/0.57    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.61/0.57  fof(f103,plain,(
% 1.61/0.57    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k1_relat_1(k5_relat_1(X0,sK0)),k1_relat_1(X0))) )),
% 1.61/0.57    inference(resolution,[],[f55,f41])).
% 1.61/0.57  fof(f41,plain,(
% 1.61/0.57    v1_relat_1(sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f38])).
% 1.61/0.57  fof(f38,plain,(
% 1.61/0.57    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.61/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f37])).
% 1.61/0.57  fof(f37,plain,(
% 1.61/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f24,plain,(
% 1.61/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f23])).
% 1.61/0.57  fof(f23,negated_conjecture,(
% 1.61/0.57    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.61/0.57    inference(negated_conjecture,[],[f22])).
% 1.61/0.57  fof(f22,conjecture,(
% 1.61/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.61/0.57  fof(f55,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f31])).
% 1.61/0.57  fof(f31,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f19])).
% 1.61/0.57  fof(f19,axiom,(
% 1.61/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 1.61/0.57  fof(f157,plain,(
% 1.61/0.57    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))),
% 1.61/0.57    inference(resolution,[],[f111,f52])).
% 1.61/0.57  fof(f52,plain,(
% 1.61/0.57    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 1.61/0.57    inference(cnf_transformation,[],[f29])).
% 1.61/0.57  fof(f29,plain,(
% 1.61/0.57    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f17])).
% 1.61/0.57  fof(f17,axiom,(
% 1.61/0.57    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 1.61/0.57  fof(f111,plain,(
% 1.61/0.57    v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.61/0.57    inference(resolution,[],[f91,f70])).
% 1.61/0.57  fof(f91,plain,(
% 1.61/0.57    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,sK0))) )),
% 1.61/0.57    inference(resolution,[],[f61,f41])).
% 1.61/0.57  fof(f61,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f36])).
% 1.61/0.57  fof(f36,plain,(
% 1.61/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.61/0.57    inference(flattening,[],[f35])).
% 1.61/0.57  fof(f35,plain,(
% 1.61/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.61/0.57    inference(ennf_transformation,[],[f15])).
% 1.61/0.57  fof(f15,axiom,(
% 1.61/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.61/0.57  fof(f42,plain,(
% 1.61/0.57    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f38])).
% 1.61/0.57  fof(f463,plain,(
% 1.61/0.57    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.61/0.57    inference(forward_demodulation,[],[f462,f47])).
% 1.61/0.57  fof(f462,plain,(
% 1.61/0.57    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)),
% 1.61/0.57    inference(forward_demodulation,[],[f455,f124])).
% 1.61/0.57  fof(f124,plain,(
% 1.61/0.57    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(X4,k1_xboole_0)) )),
% 1.61/0.57    inference(resolution,[],[f74,f49])).
% 1.61/0.57  fof(f74,plain,(
% 1.61/0.57    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) )),
% 1.61/0.57    inference(resolution,[],[f59,f43])).
% 1.61/0.57  fof(f59,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f33])).
% 1.61/0.57  fof(f33,plain,(
% 1.61/0.57    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.61/0.57    inference(ennf_transformation,[],[f10])).
% 1.61/0.57  fof(f10,axiom,(
% 1.61/0.57    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.61/0.57  fof(f455,plain,(
% 1.61/0.57    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))),
% 1.61/0.57    inference(backward_demodulation,[],[f348,f453])).
% 1.61/0.57  fof(f453,plain,(
% 1.61/0.57    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.61/0.57    inference(resolution,[],[f363,f94])).
% 1.61/0.57  fof(f363,plain,(
% 1.61/0.57    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)),
% 1.61/0.57    inference(backward_demodulation,[],[f344,f349])).
% 1.61/0.57  fof(f349,plain,(
% 1.61/0.57    k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.61/0.57    inference(resolution,[],[f318,f53])).
% 1.61/0.57  fof(f53,plain,(
% 1.61/0.57    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f30])).
% 1.61/0.57  fof(f30,plain,(
% 1.61/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f18])).
% 1.61/0.57  fof(f18,axiom,(
% 1.61/0.57    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.61/0.57  fof(f318,plain,(
% 1.61/0.57    v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.61/0.57    inference(resolution,[],[f92,f41])).
% 1.61/0.57  fof(f92,plain,(
% 1.61/0.57    ( ! [X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,k1_xboole_0))) )),
% 1.61/0.57    inference(resolution,[],[f61,f70])).
% 1.61/0.57  fof(f344,plain,(
% 1.61/0.57    r1_tarski(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0)),
% 1.61/0.57    inference(backward_demodulation,[],[f248,f336])).
% 1.61/0.57  fof(f336,plain,(
% 1.61/0.57    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.61/0.57    inference(resolution,[],[f285,f41])).
% 1.61/0.57  fof(f285,plain,(
% 1.61/0.57    ( ! [X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X1))) )),
% 1.61/0.57    inference(backward_demodulation,[],[f107,f280])).
% 1.61/0.57  fof(f280,plain,(
% 1.61/0.57    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.61/0.57    inference(forward_demodulation,[],[f279,f47])).
% 1.61/0.57  fof(f279,plain,(
% 1.61/0.57    k4_relat_1(k1_xboole_0) = k3_xboole_0(k4_relat_1(k1_xboole_0),k1_xboole_0)),
% 1.61/0.57    inference(forward_demodulation,[],[f278,f124])).
% 1.61/0.57  fof(f278,plain,(
% 1.61/0.57    k4_relat_1(k1_xboole_0) = k3_xboole_0(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0))),
% 1.61/0.57    inference(forward_demodulation,[],[f265,f83])).
% 1.61/0.57  fof(f83,plain,(
% 1.61/0.57    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 1.61/0.57    inference(forward_demodulation,[],[f82,f44])).
% 1.61/0.57  fof(f82,plain,(
% 1.61/0.57    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 1.61/0.57    inference(resolution,[],[f54,f70])).
% 1.61/0.57  fof(f54,plain,(
% 1.61/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f30])).
% 1.61/0.57  fof(f265,plain,(
% 1.61/0.57    k4_relat_1(k1_xboole_0) = k3_xboole_0(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k2_relat_1(k4_relat_1(k1_xboole_0))))),
% 1.61/0.57    inference(resolution,[],[f73,f52])).
% 1.61/0.57  fof(f73,plain,(
% 1.61/0.57    v1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.61/0.57    inference(resolution,[],[f50,f70])).
% 1.61/0.57  fof(f50,plain,(
% 1.61/0.57    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f27])).
% 1.61/0.57  fof(f27,plain,(
% 1.61/0.57    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f14])).
% 1.61/0.57  fof(f14,axiom,(
% 1.61/0.57    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.61/0.57  fof(f107,plain,(
% 1.61/0.57    ( ! [X1] : (k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.61/0.57    inference(resolution,[],[f56,f70])).
% 1.61/0.57  fof(f56,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f32])).
% 1.61/0.57  fof(f32,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f20])).
% 1.61/0.57  fof(f20,axiom,(
% 1.61/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 1.61/0.57  fof(f248,plain,(
% 1.61/0.57    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_xboole_0)),
% 1.61/0.57    inference(forward_demodulation,[],[f242,f44])).
% 1.61/0.57  fof(f242,plain,(
% 1.61/0.57    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_relat_1(k1_xboole_0))),
% 1.61/0.57    inference(resolution,[],[f105,f70])).
% 1.61/0.57  fof(f105,plain,(
% 1.61/0.57    ( ! [X2] : (~v1_relat_1(X2) | r1_tarski(k1_relat_1(k5_relat_1(X2,k4_relat_1(sK0))),k1_relat_1(X2))) )),
% 1.61/0.57    inference(resolution,[],[f55,f72])).
% 1.61/0.57  fof(f72,plain,(
% 1.61/0.57    v1_relat_1(k4_relat_1(sK0))),
% 1.61/0.57    inference(resolution,[],[f50,f41])).
% 1.61/0.57  fof(f348,plain,(
% 1.61/0.57    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))),
% 1.61/0.57    inference(resolution,[],[f318,f52])).
% 1.61/0.57  % SZS output end Proof for theBenchmark
% 1.61/0.57  % (20254)------------------------------
% 1.61/0.57  % (20254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (20254)Termination reason: Refutation
% 1.61/0.57  
% 1.61/0.57  % (20254)Memory used [KB]: 2046
% 1.61/0.57  % (20254)Time elapsed: 0.164 s
% 1.61/0.57  % (20254)------------------------------
% 1.61/0.57  % (20254)------------------------------
% 1.61/0.57  % (20246)Success in time 0.216 s
%------------------------------------------------------------------------------
