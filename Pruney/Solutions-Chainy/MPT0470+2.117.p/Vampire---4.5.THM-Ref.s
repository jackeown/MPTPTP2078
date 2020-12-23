%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:01 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 482 expanded)
%              Number of leaves         :   14 ( 125 expanded)
%              Depth                    :   18
%              Number of atoms          :  170 ( 962 expanded)
%              Number of equality atoms :   58 ( 348 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2027,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2026,f285])).

fof(f285,plain,(
    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f28,f284])).

fof(f284,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f282,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f282,plain,(
    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f122,f278])).

fof(f278,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f88,f29])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f88,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(k1_xboole_0,X1)) ) ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f64,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f52,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f52,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f43,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f122,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f121,f30])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f121,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f39,f76])).

fof(f76,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f72,f29])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(forward_demodulation,[],[f71,f31])).

fof(f31,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(subsumption_resolution,[],[f70,f64])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(subsumption_resolution,[],[f68,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(superposition,[],[f38,f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f28,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f2026,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1996,f1768])).

fof(f1768,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f428,f1765])).

fof(f1765,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f1269,f34])).

fof(f1269,plain,(
    v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f1268,f268])).

fof(f268,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f88,f85])).

fof(f85,plain,(
    v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f64,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f1268,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f1266,f30])).

fof(f1266,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) ),
    inference(superposition,[],[f39,f98])).

fof(f98,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f85,f72])).

fof(f428,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) ),
    inference(forward_demodulation,[],[f411,f86])).

fof(f86,plain,(
    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f64,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f411,plain,(
    k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = k5_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f87,f85])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k1_xboole_0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f64,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f1996,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f137,f1994])).

fof(f1994,plain,(
    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1793,f244])).

fof(f244,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) ),
    inference(resolution,[],[f238,f34])).

fof(f238,plain,(
    v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f132,f237])).

fof(f237,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f228,f101])).

fof(f101,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) ),
    inference(forward_demodulation,[],[f97,f86])).

fof(f97,plain,(
    k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) = k5_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(sK0)) ),
    inference(resolution,[],[f85,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(sK0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f37,f29])).

fof(f228,plain,(
    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0)))) ),
    inference(resolution,[],[f96,f35])).

fof(f96,plain,(
    v1_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f85,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(sK0,X0)) ) ),
    inference(resolution,[],[f44,f29])).

fof(f132,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f131,f30])).

fof(f131,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(superposition,[],[f39,f77])).

fof(f77,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f72,f51])).

fof(f51,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f35,f29])).

fof(f1793,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f90,f1768])).

fof(f90,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) ),
    inference(resolution,[],[f64,f65])).

fof(f137,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f89,f36])).

fof(f89,plain,(
    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f64,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:20:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (21178)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (21170)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (21164)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (21173)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (21165)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (21177)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (21161)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (21172)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (21176)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (21179)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (21167)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (21174)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (21161)Refutation not found, incomplete strategy% (21161)------------------------------
% 0.21/0.49  % (21161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21161)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (21161)Memory used [KB]: 10618
% 0.21/0.49  % (21161)Time elapsed: 0.054 s
% 0.21/0.49  % (21161)------------------------------
% 0.21/0.49  % (21161)------------------------------
% 0.21/0.50  % (21166)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (21163)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (21171)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (21168)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (21160)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (21169)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (21180)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (21180)Refutation not found, incomplete strategy% (21180)------------------------------
% 0.21/0.50  % (21180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21180)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21180)Memory used [KB]: 10618
% 0.21/0.50  % (21180)Time elapsed: 0.098 s
% 0.21/0.50  % (21180)------------------------------
% 0.21/0.50  % (21180)------------------------------
% 0.21/0.51  % (21162)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.34/0.53  % (21175)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.48/0.59  % (21177)Refutation found. Thanks to Tanya!
% 1.48/0.59  % SZS status Theorem for theBenchmark
% 1.48/0.59  % SZS output start Proof for theBenchmark
% 1.48/0.59  fof(f2027,plain,(
% 1.48/0.59    $false),
% 1.48/0.59    inference(subsumption_resolution,[],[f2026,f285])).
% 1.48/0.59  fof(f285,plain,(
% 1.48/0.59    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.48/0.59    inference(subsumption_resolution,[],[f28,f284])).
% 1.48/0.59  fof(f284,plain,(
% 1.48/0.59    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.48/0.59    inference(resolution,[],[f282,f34])).
% 1.48/0.59  fof(f34,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.48/0.59    inference(cnf_transformation,[],[f17])).
% 1.48/0.59  fof(f17,plain,(
% 1.48/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f2])).
% 1.48/0.59  fof(f2,axiom,(
% 1.48/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.48/0.59  fof(f282,plain,(
% 1.48/0.59    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.59    inference(subsumption_resolution,[],[f122,f278])).
% 1.48/0.59  fof(f278,plain,(
% 1.48/0.59    v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.59    inference(resolution,[],[f88,f29])).
% 1.48/0.59  fof(f29,plain,(
% 1.48/0.59    v1_relat_1(sK0)),
% 1.48/0.59    inference(cnf_transformation,[],[f16])).
% 1.48/0.59  fof(f16,plain,(
% 1.48/0.59    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f15])).
% 1.48/0.59  fof(f15,negated_conjecture,(
% 1.48/0.59    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.48/0.59    inference(negated_conjecture,[],[f14])).
% 1.48/0.59  fof(f14,conjecture,(
% 1.48/0.59    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.48/0.59  fof(f88,plain,(
% 1.48/0.59    ( ! [X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(k1_xboole_0,X1))) )),
% 1.48/0.59    inference(resolution,[],[f64,f44])).
% 1.48/0.59  fof(f44,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 1.48/0.59    inference(cnf_transformation,[],[f27])).
% 1.48/0.59  fof(f27,plain,(
% 1.48/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(flattening,[],[f26])).
% 1.48/0.59  fof(f26,plain,(
% 1.48/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.48/0.59    inference(ennf_transformation,[],[f8])).
% 1.48/0.59  fof(f8,axiom,(
% 1.48/0.59    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.48/0.59  fof(f64,plain,(
% 1.48/0.59    v1_relat_1(k1_xboole_0)),
% 1.48/0.59    inference(resolution,[],[f52,f41])).
% 1.48/0.59  fof(f41,plain,(
% 1.48/0.59    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f25])).
% 1.48/0.59  fof(f25,plain,(
% 1.48/0.59    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.48/0.59    inference(ennf_transformation,[],[f6])).
% 1.48/0.59  fof(f6,axiom,(
% 1.48/0.59    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 1.48/0.59  fof(f52,plain,(
% 1.48/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.48/0.59    inference(superposition,[],[f43,f48])).
% 1.48/0.59  fof(f48,plain,(
% 1.48/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.48/0.59    inference(equality_resolution,[],[f47])).
% 1.48/0.59  fof(f47,plain,(
% 1.48/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f4])).
% 1.48/0.59  fof(f4,axiom,(
% 1.48/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.48/0.59  fof(f43,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.48/0.59    inference(cnf_transformation,[],[f5])).
% 1.48/0.59  fof(f5,axiom,(
% 1.48/0.59    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.48/0.59  fof(f122,plain,(
% 1.48/0.59    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.59    inference(subsumption_resolution,[],[f121,f30])).
% 1.48/0.59  fof(f30,plain,(
% 1.48/0.59    v1_xboole_0(k1_xboole_0)),
% 1.48/0.59    inference(cnf_transformation,[],[f1])).
% 1.48/0.59  fof(f1,axiom,(
% 1.48/0.59    v1_xboole_0(k1_xboole_0)),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.48/0.59  fof(f121,plain,(
% 1.48/0.59    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.59    inference(superposition,[],[f39,f76])).
% 1.48/0.59  fof(f76,plain,(
% 1.48/0.59    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.59    inference(resolution,[],[f72,f29])).
% 1.48/0.59  fof(f72,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.48/0.59    inference(forward_demodulation,[],[f71,f31])).
% 1.48/0.59  fof(f31,plain,(
% 1.48/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.48/0.59    inference(cnf_transformation,[],[f13])).
% 1.48/0.59  fof(f13,axiom,(
% 1.48/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.48/0.59  fof(f71,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f70,f64])).
% 1.48/0.59  fof(f70,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.48/0.59    inference(subsumption_resolution,[],[f68,f33])).
% 1.48/0.59  fof(f33,plain,(
% 1.48/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f3])).
% 1.48/0.59  fof(f3,axiom,(
% 1.48/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.48/0.59  fof(f68,plain,(
% 1.48/0.59    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.48/0.59    inference(superposition,[],[f38,f32])).
% 1.48/0.59  fof(f32,plain,(
% 1.48/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.48/0.59    inference(cnf_transformation,[],[f13])).
% 1.48/0.59  fof(f38,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))) )),
% 1.48/0.59    inference(cnf_transformation,[],[f22])).
% 1.48/0.59  fof(f22,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(flattening,[],[f21])).
% 1.48/0.59  fof(f21,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f11])).
% 1.48/0.59  fof(f11,axiom,(
% 1.48/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 1.48/0.59  fof(f39,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f24])).
% 1.48/0.59  fof(f24,plain,(
% 1.48/0.59    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.48/0.59    inference(flattening,[],[f23])).
% 1.48/0.59  fof(f23,plain,(
% 1.48/0.59    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.48/0.59    inference(ennf_transformation,[],[f9])).
% 1.48/0.59  fof(f9,axiom,(
% 1.48/0.59    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 1.48/0.59  fof(f28,plain,(
% 1.48/0.59    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.48/0.59    inference(cnf_transformation,[],[f16])).
% 1.48/0.59  fof(f2026,plain,(
% 1.48/0.59    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.48/0.59    inference(forward_demodulation,[],[f1996,f1768])).
% 1.48/0.59  fof(f1768,plain,(
% 1.48/0.59    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.48/0.59    inference(backward_demodulation,[],[f428,f1765])).
% 1.48/0.59  fof(f1765,plain,(
% 1.48/0.59    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))),
% 1.48/0.59    inference(resolution,[],[f1269,f34])).
% 1.48/0.59  fof(f1269,plain,(
% 1.48/0.59    v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))),
% 1.48/0.59    inference(subsumption_resolution,[],[f1268,f268])).
% 1.48/0.59  fof(f268,plain,(
% 1.48/0.59    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))),
% 1.48/0.59    inference(resolution,[],[f88,f85])).
% 1.48/0.59  fof(f85,plain,(
% 1.48/0.59    v1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.48/0.59    inference(resolution,[],[f64,f35])).
% 1.48/0.59  fof(f35,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f18,plain,(
% 1.48/0.59    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f7])).
% 1.48/0.59  fof(f7,axiom,(
% 1.48/0.59    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.48/0.59  fof(f1268,plain,(
% 1.48/0.59    ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))),
% 1.48/0.59    inference(subsumption_resolution,[],[f1266,f30])).
% 1.48/0.59  fof(f1266,plain,(
% 1.48/0.59    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))),
% 1.48/0.59    inference(superposition,[],[f39,f98])).
% 1.48/0.59  fof(f98,plain,(
% 1.48/0.59    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))),
% 1.48/0.59    inference(resolution,[],[f85,f72])).
% 1.48/0.59  fof(f428,plain,(
% 1.48/0.59    k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))),
% 1.48/0.59    inference(forward_demodulation,[],[f411,f86])).
% 1.48/0.59  fof(f86,plain,(
% 1.48/0.59    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0))),
% 1.48/0.59    inference(resolution,[],[f64,f36])).
% 1.48/0.59  fof(f36,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 1.48/0.59    inference(cnf_transformation,[],[f19])).
% 1.48/0.59  fof(f19,plain,(
% 1.48/0.59    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f10])).
% 1.48/0.59  fof(f10,axiom,(
% 1.48/0.59    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.48/0.59  fof(f411,plain,(
% 1.48/0.59    k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = k5_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(k1_xboole_0))),
% 1.48/0.59    inference(resolution,[],[f87,f85])).
% 1.48/0.59  fof(f87,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k1_xboole_0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0))) )),
% 1.48/0.59    inference(resolution,[],[f64,f37])).
% 1.48/0.59  fof(f37,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 1.48/0.59    inference(cnf_transformation,[],[f20])).
% 1.48/0.59  fof(f20,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f12])).
% 1.48/0.59  fof(f12,axiom,(
% 1.48/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.48/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.48/0.59  fof(f1996,plain,(
% 1.48/0.59    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)),
% 1.48/0.59    inference(backward_demodulation,[],[f137,f1994])).
% 1.48/0.59  fof(f1994,plain,(
% 1.48/0.59    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.48/0.59    inference(forward_demodulation,[],[f1793,f244])).
% 1.48/0.59  fof(f244,plain,(
% 1.48/0.59    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),
% 1.48/0.59    inference(resolution,[],[f238,f34])).
% 1.48/0.59  fof(f238,plain,(
% 1.48/0.59    v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.48/0.59    inference(subsumption_resolution,[],[f132,f237])).
% 1.48/0.59  fof(f237,plain,(
% 1.48/0.59    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.48/0.59    inference(forward_demodulation,[],[f228,f101])).
% 1.48/0.59  fof(f101,plain,(
% 1.48/0.59    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0)))),
% 1.48/0.59    inference(forward_demodulation,[],[f97,f86])).
% 1.48/0.59  fof(f97,plain,(
% 1.48/0.59    k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) = k5_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(sK0))),
% 1.48/0.59    inference(resolution,[],[f85,f65])).
% 1.48/0.59  fof(f65,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(sK0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(sK0))) )),
% 1.48/0.59    inference(resolution,[],[f37,f29])).
% 1.48/0.59  fof(f228,plain,(
% 1.48/0.59    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))))),
% 1.48/0.59    inference(resolution,[],[f96,f35])).
% 1.48/0.59  fof(f96,plain,(
% 1.48/0.59    v1_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0)))),
% 1.48/0.59    inference(resolution,[],[f85,f59])).
% 1.48/0.59  fof(f59,plain,(
% 1.48/0.59    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(sK0,X0))) )),
% 1.48/0.59    inference(resolution,[],[f44,f29])).
% 1.48/0.59  fof(f132,plain,(
% 1.48/0.59    ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.48/0.59    inference(subsumption_resolution,[],[f131,f30])).
% 1.48/0.59  fof(f131,plain,(
% 1.48/0.59    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.48/0.59    inference(superposition,[],[f39,f77])).
% 1.48/0.59  fof(f77,plain,(
% 1.48/0.59    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.48/0.59    inference(resolution,[],[f72,f51])).
% 1.48/0.59  fof(f51,plain,(
% 1.48/0.59    v1_relat_1(k4_relat_1(sK0))),
% 1.48/0.59    inference(resolution,[],[f35,f29])).
% 1.48/0.59  fof(f1793,plain,(
% 1.48/0.59    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.48/0.59    inference(backward_demodulation,[],[f90,f1768])).
% 1.48/0.59  fof(f90,plain,(
% 1.48/0.59    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0))),
% 1.48/0.59    inference(resolution,[],[f64,f65])).
% 1.48/0.59  fof(f137,plain,(
% 1.48/0.59    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 1.48/0.59    inference(resolution,[],[f89,f36])).
% 1.48/0.59  fof(f89,plain,(
% 1.48/0.59    v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.48/0.59    inference(resolution,[],[f64,f59])).
% 1.48/0.59  % SZS output end Proof for theBenchmark
% 1.48/0.59  % (21177)------------------------------
% 1.48/0.59  % (21177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.59  % (21177)Termination reason: Refutation
% 1.48/0.59  
% 1.48/0.59  % (21177)Memory used [KB]: 3326
% 1.48/0.59  % (21177)Time elapsed: 0.164 s
% 1.48/0.59  % (21177)------------------------------
% 1.48/0.59  % (21177)------------------------------
% 1.48/0.60  % (21159)Success in time 0.237 s
%------------------------------------------------------------------------------
