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
% DateTime   : Thu Dec  3 12:47:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 160 expanded)
%              Number of leaves         :   17 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  196 ( 382 expanded)
%              Number of equality atoms :   34 (  98 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(subsumption_resolution,[],[f161,f102])).

fof(f102,plain,(
    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f39,f101])).

fof(f101,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f99,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f99,plain,(
    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f98,f40])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f98,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f97,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f97,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f95,f38])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f95,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f84,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f84,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f80,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f48,f74])).

fof(f74,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f73,f38])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f72,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f61,f43])).

fof(f43,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f60,f45])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f53,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k3_xboole_0(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) ) ),
    inference(resolution,[],[f71,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f71,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f70,f40])).

fof(f70,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f69,f44])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f42])).

fof(f42,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f39,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f161,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f159,f45])).

fof(f159,plain,(
    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f158,f40])).

fof(f158,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f157,f44])).

fof(f157,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f155,f38])).

fof(f155,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f154,f55])).

fof(f154,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f152,f40])).

fof(f152,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f49,f147])).

fof(f147,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f146,f62])).

fof(f146,plain,(
    k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) ),
    inference(resolution,[],[f145,f54])).

fof(f145,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f144,f40])).

fof(f144,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f143,f44])).

fof(f143,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) ),
    inference(superposition,[],[f139,f41])).

fof(f41,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f139,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,sK0)),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f47,f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:59:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (8073)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.47  % (8068)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.48  % (8062)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (8064)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (8069)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (8064)Refutation not found, incomplete strategy% (8064)------------------------------
% 0.21/0.49  % (8064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8064)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (8064)Memory used [KB]: 6012
% 0.21/0.49  % (8064)Time elapsed: 0.085 s
% 0.21/0.49  % (8064)------------------------------
% 0.21/0.49  % (8064)------------------------------
% 0.21/0.49  % (8058)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.49  % (8061)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (8079)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.49  % (8059)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (8071)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (8075)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (8077)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (8078)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (8076)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (8057)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (8076)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f161,f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f39,f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.50    inference(resolution,[],[f99,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f98,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(resolution,[],[f97,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ~v1_relat_1(k1_xboole_0) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f95,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    v1_relat_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.21/0.50    inference(resolution,[],[f84,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f80,f40])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.50    inference(superposition,[],[f48,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.50    inference(resolution,[],[f73,f38])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f72,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f61,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f60,f45])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f53,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(rectify,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k3_xboole_0(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f71,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f70,f40])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_xboole_0(k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f69,f44])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(superposition,[],[f46,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.50    inference(resolution,[],[f159,f45])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f158,f40])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(resolution,[],[f157,f44])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ~v1_relat_1(k1_xboole_0) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f155,f38])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(resolution,[],[f154,f55])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f152,f40])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.50    inference(superposition,[],[f49,f147])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.50    inference(forward_demodulation,[],[f146,f62])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)),
% 0.21/0.50    inference(resolution,[],[f145,f54])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f144,f40])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(resolution,[],[f143,f44])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)),
% 0.21/0.50    inference(superposition,[],[f139,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(X0,sK0)),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(resolution,[],[f47,f38])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (8076)------------------------------
% 0.21/0.50  % (8076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8076)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (8076)Memory used [KB]: 6140
% 0.21/0.50  % (8076)Time elapsed: 0.107 s
% 0.21/0.50  % (8076)------------------------------
% 0.21/0.50  % (8076)------------------------------
% 0.21/0.50  % (8056)Success in time 0.152 s
%------------------------------------------------------------------------------
