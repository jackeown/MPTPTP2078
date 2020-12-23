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
% DateTime   : Thu Dec  3 12:47:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 (2501 expanded)
%              Number of leaves         :   16 ( 769 expanded)
%              Depth                    :   30
%              Number of atoms          :  231 (4471 expanded)
%              Number of equality atoms :   73 (1107 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f596,plain,(
    $false ),
    inference(subsumption_resolution,[],[f595,f416])).

fof(f416,plain,(
    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f35,f402])).

fof(f402,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f401,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f401,plain,(
    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f400,f34])).

fof(f34,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

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

fof(f400,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f398,f89])).

fof(f89,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f66,f88])).

fof(f88,plain,(
    v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f87,f56])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f52,f55])).

fof(f55,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f40,f52])).

fof(f52,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f32])).

fof(f32,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK1) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f87,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f85,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f85,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f84,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f84,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f83,f56])).

fof(f83,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(superposition,[],[f47,f82])).

fof(f82,plain,(
    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f81,f36])).

fof(f36,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f81,plain,(
    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f71,f56])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(resolution,[],[f44,f39])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f66,plain,
    ( ~ v1_xboole_0(k4_relat_1(k1_xboole_0))
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f64,f39])).

fof(f64,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f41,f63])).

fof(f63,plain,(
    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f59,f56])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f42,f39])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f398,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f376,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f376,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f374,f366])).

fof(f366,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f359,f257])).

fof(f257,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f252,f98])).

fof(f98,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f88,f40])).

fof(f252,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) ),
    inference(resolution,[],[f154,f89])).

fof(f154,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k4_relat_1(k5_relat_1(sK0,X8)) = k5_relat_1(k4_relat_1(X8),k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f46,f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f359,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f357,f89])).

fof(f357,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | k5_relat_1(sK0,X11) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X11))) ) ),
    inference(resolution,[],[f76,f34])).

fof(f76,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4)
      | k5_relat_1(X5,X4) = k4_relat_1(k4_relat_1(k5_relat_1(X5,X4))) ) ),
    inference(resolution,[],[f48,f42])).

fof(f374,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) ),
    inference(backward_demodulation,[],[f286,f366])).

fof(f286,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) ),
    inference(subsumption_resolution,[],[f285,f56])).

fof(f285,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) ),
    inference(superposition,[],[f47,f278])).

fof(f278,plain,(
    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) ),
    inference(forward_demodulation,[],[f266,f173])).

fof(f173,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f158,f34])).

fof(f158,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X1))) ) ),
    inference(resolution,[],[f148,f41])).

fof(f148,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(resolution,[],[f147,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f51,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

% (27434)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f147,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f145,f89])).

fof(f145,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f45,f36])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f266,plain,(
    k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) ),
    inference(resolution,[],[f262,f44])).

fof(f262,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f261,f34])).

fof(f261,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f259,f89])).

fof(f259,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f258,f48])).

fof(f258,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(superposition,[],[f41,f257])).

fof(f35,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f595,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f585,f98])).

fof(f585,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f550,f566])).

fof(f566,plain,(
    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) ),
    inference(resolution,[],[f565,f40])).

fof(f565,plain,(
    v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f564,f215])).

fof(f215,plain,(
    v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f214,f89])).

fof(f214,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f212,f34])).

fof(f212,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f211,f48])).

fof(f211,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(superposition,[],[f41,f208])).

fof(f208,plain,(
    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) ),
    inference(resolution,[],[f155,f34])).

fof(f155,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k4_relat_1(k5_relat_1(k1_xboole_0,X2)) = k5_relat_1(k4_relat_1(X2),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f151,f98])).

fof(f151,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k4_relat_1(k5_relat_1(k1_xboole_0,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f46,f89])).

fof(f564,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f563,f56])).

fof(f563,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(superposition,[],[f47,f560])).

fof(f560,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f552,f160])).

fof(f160,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f148,f34])).

fof(f552,plain,(
    k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f217,f550])).

fof(f217,plain,(
    k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k1_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) ),
    inference(resolution,[],[f215,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f550,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f545,f208])).

fof(f545,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(resolution,[],[f351,f34])).

fof(f351,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k1_xboole_0,X2) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X2))) ) ),
    inference(resolution,[],[f76,f89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:19:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.48  % (27431)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (27420)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (27440)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (27423)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (27429)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (27422)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (27445)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (27424)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (27436)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (27437)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (27419)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (27442)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (27433)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (27438)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (27425)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (27428)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (27427)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (27422)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f596,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f595,f416])).
% 0.20/0.53  fof(f416,plain,(
% 0.20/0.53    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f35,f402])).
% 0.20/0.53  fof(f402,plain,(
% 0.20/0.53    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f401,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.53  fof(f401,plain,(
% 0.20/0.53    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f400,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    v1_relat_1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.53    inference(negated_conjecture,[],[f14])).
% 0.20/0.53  fof(f14,conjecture,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.53  fof(f400,plain,(
% 0.20/0.53    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f398,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    v1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f66,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f87,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(backward_demodulation,[],[f52,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    k1_xboole_0 = sK1),
% 0.20/0.53    inference(resolution,[],[f40,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    v1_xboole_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    v1_xboole_0(sK1)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK1)),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ? [X0] : v1_xboole_0(X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f85,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ~v1_relat_1(k1_xboole_0) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 0.20/0.53    inference(resolution,[],[f84,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f83,f56])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 0.20/0.53    inference(superposition,[],[f47,f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 0.20/0.53    inference(forward_demodulation,[],[f81,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 0.20/0.53    inference(resolution,[],[f71,f56])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.20/0.53    inference(resolution,[],[f44,f39])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ~v1_xboole_0(k4_relat_1(k1_xboole_0)) | v1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f64,f39])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(superposition,[],[f41,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0))),
% 0.20/0.53    inference(resolution,[],[f59,f56])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 0.20/0.53    inference(resolution,[],[f42,f39])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.20/0.53  fof(f398,plain,(
% 0.20/0.53    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.20/0.53    inference(resolution,[],[f376,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.53  fof(f376,plain,(
% 0.20/0.53    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.53    inference(forward_demodulation,[],[f374,f366])).
% 0.20/0.53  fof(f366,plain,(
% 0.20/0.53    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 0.20/0.53    inference(forward_demodulation,[],[f359,f257])).
% 0.20/0.53  fof(f257,plain,(
% 0.20/0.53    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.53    inference(forward_demodulation,[],[f252,f98])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f88,f40])).
% 0.20/0.53  fof(f252,plain,(
% 0.20/0.53    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0))),
% 0.20/0.53    inference(resolution,[],[f154,f89])).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    ( ! [X8] : (~v1_relat_1(X8) | k4_relat_1(k5_relat_1(sK0,X8)) = k5_relat_1(k4_relat_1(X8),k4_relat_1(sK0))) )),
% 0.20/0.53    inference(resolution,[],[f46,f34])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.20/0.53  fof(f359,plain,(
% 0.20/0.53    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.20/0.53    inference(resolution,[],[f357,f89])).
% 0.20/0.53  fof(f357,plain,(
% 0.20/0.53    ( ! [X11] : (~v1_relat_1(X11) | k5_relat_1(sK0,X11) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X11)))) )),
% 0.20/0.53    inference(resolution,[],[f76,f34])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X4,X5] : (~v1_relat_1(X5) | ~v1_relat_1(X4) | k5_relat_1(X5,X4) = k4_relat_1(k4_relat_1(k5_relat_1(X5,X4)))) )),
% 0.20/0.53    inference(resolution,[],[f48,f42])).
% 0.20/0.53  fof(f374,plain,(
% 0.20/0.53    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))),
% 0.20/0.53    inference(backward_demodulation,[],[f286,f366])).
% 0.20/0.53  fof(f286,plain,(
% 0.20/0.53    ~v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))),
% 0.20/0.53    inference(subsumption_resolution,[],[f285,f56])).
% 0.20/0.53  fof(f285,plain,(
% 0.20/0.53    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))),
% 0.20/0.53    inference(superposition,[],[f47,f278])).
% 0.20/0.53  fof(f278,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))),
% 0.20/0.53    inference(forward_demodulation,[],[f266,f173])).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 0.20/0.53    inference(resolution,[],[f158,f34])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X1)))) )),
% 0.20/0.53    inference(resolution,[],[f148,f41])).
% 0.20/0.53  fof(f148,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 0.20/0.53    inference(resolution,[],[f147,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(resolution,[],[f51,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  % (27434)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f145,f89])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.53    inference(superposition,[],[f45,f36])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.20/0.53  fof(f266,plain,(
% 0.20/0.53    k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))),
% 0.20/0.53    inference(resolution,[],[f262,f44])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f261,f34])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f259,f89])).
% 0.20/0.53  fof(f259,plain,(
% 0.20/0.53    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.20/0.53    inference(resolution,[],[f258,f48])).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 0.20/0.53    inference(superposition,[],[f41,f257])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f595,plain,(
% 0.20/0.53    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.53    inference(forward_demodulation,[],[f585,f98])).
% 0.20/0.53  fof(f585,plain,(
% 0.20/0.53    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(backward_demodulation,[],[f550,f566])).
% 0.20/0.53  fof(f566,plain,(
% 0.20/0.53    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f565,f40])).
% 0.20/0.53  fof(f565,plain,(
% 0.20/0.53    v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f564,f215])).
% 0.20/0.53  fof(f215,plain,(
% 0.20/0.53    v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f214,f89])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f212,f34])).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f211,f48])).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.20/0.53    inference(superposition,[],[f41,f208])).
% 0.20/0.53  fof(f208,plain,(
% 0.20/0.53    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f155,f34])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    ( ! [X2] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(k1_xboole_0,X2)) = k5_relat_1(k4_relat_1(X2),k1_xboole_0)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f151,f98])).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    ( ! [X2] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(k1_xboole_0,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k1_xboole_0))) )),
% 0.20/0.53    inference(resolution,[],[f46,f89])).
% 0.20/0.53  fof(f564,plain,(
% 0.20/0.53    ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f563,f56])).
% 0.20/0.53  fof(f563,plain,(
% 0.20/0.53    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.20/0.53    inference(superposition,[],[f47,f560])).
% 0.20/0.53  fof(f560,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.20/0.53    inference(forward_demodulation,[],[f552,f160])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.53    inference(resolution,[],[f148,f34])).
% 0.20/0.53  fof(f552,plain,(
% 0.20/0.53    k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.20/0.53    inference(backward_demodulation,[],[f217,f550])).
% 0.20/0.53  fof(f217,plain,(
% 0.20/0.53    k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k1_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))),
% 0.20/0.53    inference(resolution,[],[f215,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f550,plain,(
% 0.20/0.53    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.20/0.53    inference(forward_demodulation,[],[f545,f208])).
% 0.20/0.53  fof(f545,plain,(
% 0.20/0.53    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 0.20/0.53    inference(resolution,[],[f351,f34])).
% 0.20/0.53  fof(f351,plain,(
% 0.20/0.53    ( ! [X2] : (~v1_relat_1(X2) | k5_relat_1(k1_xboole_0,X2) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X2)))) )),
% 0.20/0.53    inference(resolution,[],[f76,f89])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (27422)------------------------------
% 0.20/0.53  % (27422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27422)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (27422)Memory used [KB]: 6524
% 0.20/0.53  % (27422)Time elapsed: 0.140 s
% 0.20/0.53  % (27422)------------------------------
% 0.20/0.53  % (27422)------------------------------
% 0.20/0.53  % (27418)Success in time 0.18 s
%------------------------------------------------------------------------------
