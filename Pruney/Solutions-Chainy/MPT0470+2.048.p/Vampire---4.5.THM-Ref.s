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
% DateTime   : Thu Dec  3 12:47:50 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 373 expanded)
%              Number of leaves         :   17 (  94 expanded)
%              Depth                    :   21
%              Number of atoms          :  218 ( 893 expanded)
%              Number of equality atoms :   49 ( 125 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2276,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2275,f567])).

fof(f567,plain,(
    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f40,f565])).

fof(f565,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f543,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f543,plain,(
    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f542,f126])).

fof(f126,plain,(
    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f86,f71])).

fof(f71,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f45,f42])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(sK0,X0)) ) ),
    inference(resolution,[],[f66,f41])).

fof(f41,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f542,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f541,f42])).

fof(f541,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f56,f216])).

fof(f216,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f215,f163])).

fof(f163,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0) ),
    inference(resolution,[],[f130,f81])).

fof(f81,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | k1_xboole_0 = k3_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f60,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f130,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f84,f42])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f64,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f215,plain,(
    k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f135,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f135,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f132,f44])).

fof(f44,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f132,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f99,f71])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(X0)) ) ),
    inference(resolution,[],[f50,f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f40,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f2275,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f2205,f721])).

fof(f721,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f703,f701])).

fof(f701,plain,(
    ! [X5] : ~ r2_hidden(X5,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f700,f129])).

fof(f129,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f82,f42])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f63,f58])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f700,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X4) ) ),
    inference(superposition,[],[f60,f137])).

fof(f137,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f81,f129])).

fof(f703,plain,
    ( r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f415,f701])).

fof(f415,plain,
    ( r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f110,f71])).

fof(f110,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK4(k1_xboole_0,X1),sK3(k1_xboole_0,X1)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK3(k1_xboole_0,X1),sK4(k1_xboole_0,X1)),X1)
      | k4_relat_1(k1_xboole_0) = X1 ) ),
    inference(resolution,[],[f54,f71])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | k4_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(f2205,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f265,f2202])).

fof(f2202,plain,(
    k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f2066,f46])).

fof(f2066,plain,(
    v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(subsumption_resolution,[],[f2065,f264])).

fof(f264,plain,(
    v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(resolution,[],[f257,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f257,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f87,f41])).

fof(f87,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(k1_xboole_0,X1)) ) ),
    inference(resolution,[],[f66,f71])).

fof(f2065,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(subsumption_resolution,[],[f2064,f42])).

fof(f2064,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(superposition,[],[f56,f1016])).

fof(f1016,plain,(
    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f1015,f163])).

fof(f1015,plain,(
    k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k3_xboole_0(k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0) ),
    inference(resolution,[],[f849,f65])).

fof(f849,plain,(
    r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f289,f757])).

fof(f757,plain,(
    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f360,f721])).

fof(f360,plain,(
    k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f106,f41])).

fof(f106,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(k1_xboole_0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f51,f71])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f289,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f280,f44])).

fof(f280,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f101,f71])).

fof(f101,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k2_relat_1(k5_relat_1(k4_relat_1(sK0),X2)),k2_relat_1(X2)) ) ),
    inference(resolution,[],[f50,f73])).

fof(f73,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f47,f41])).

fof(f265,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(resolution,[],[f257,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (12836)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (12839)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (12837)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (12843)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (12854)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (12855)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (12851)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (12841)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (12838)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (12849)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (12837)Refutation not found, incomplete strategy% (12837)------------------------------
% 0.20/0.49  % (12837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (12837)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (12837)Memory used [KB]: 10618
% 0.20/0.49  % (12837)Time elapsed: 0.080 s
% 0.20/0.49  % (12837)------------------------------
% 0.20/0.49  % (12837)------------------------------
% 0.20/0.50  % (12856)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (12856)Refutation not found, incomplete strategy% (12856)------------------------------
% 0.20/0.50  % (12856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12856)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (12856)Memory used [KB]: 10618
% 0.20/0.50  % (12856)Time elapsed: 0.084 s
% 0.20/0.50  % (12856)------------------------------
% 0.20/0.50  % (12856)------------------------------
% 0.20/0.50  % (12842)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (12840)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (12847)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (12848)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (12846)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (12853)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (12850)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (12845)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (12852)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.52  % (12844)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.75/0.62  % (12853)Refutation found. Thanks to Tanya!
% 1.75/0.62  % SZS status Theorem for theBenchmark
% 2.10/0.63  % SZS output start Proof for theBenchmark
% 2.10/0.63  fof(f2276,plain,(
% 2.10/0.63    $false),
% 2.10/0.63    inference(subsumption_resolution,[],[f2275,f567])).
% 2.10/0.63  fof(f567,plain,(
% 2.10/0.63    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 2.10/0.63    inference(subsumption_resolution,[],[f40,f565])).
% 2.10/0.63  fof(f565,plain,(
% 2.10/0.63    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 2.10/0.63    inference(resolution,[],[f543,f46])).
% 2.10/0.63  fof(f46,plain,(
% 2.10/0.63    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.10/0.63    inference(cnf_transformation,[],[f24])).
% 2.10/0.63  fof(f24,plain,(
% 2.10/0.63    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f3])).
% 2.10/0.63  fof(f3,axiom,(
% 2.10/0.63    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.10/0.63  fof(f543,plain,(
% 2.10/0.63    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 2.10/0.63    inference(subsumption_resolution,[],[f542,f126])).
% 2.10/0.63  fof(f126,plain,(
% 2.10/0.63    v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 2.10/0.63    inference(resolution,[],[f86,f71])).
% 2.10/0.63  fof(f71,plain,(
% 2.10/0.63    v1_relat_1(k1_xboole_0)),
% 2.10/0.63    inference(resolution,[],[f45,f42])).
% 2.10/0.63  fof(f42,plain,(
% 2.10/0.63    v1_xboole_0(k1_xboole_0)),
% 2.10/0.63    inference(cnf_transformation,[],[f2])).
% 2.10/0.63  fof(f2,axiom,(
% 2.10/0.63    v1_xboole_0(k1_xboole_0)),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.10/0.63  fof(f45,plain,(
% 2.10/0.63    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f23])).
% 2.10/0.63  fof(f23,plain,(
% 2.10/0.63    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f8])).
% 2.10/0.63  fof(f8,axiom,(
% 2.10/0.63    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 2.10/0.63  fof(f86,plain,(
% 2.10/0.63    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(sK0,X0))) )),
% 2.10/0.63    inference(resolution,[],[f66,f41])).
% 2.10/0.63  fof(f41,plain,(
% 2.10/0.63    v1_relat_1(sK0)),
% 2.10/0.63    inference(cnf_transformation,[],[f22])).
% 2.10/0.63  fof(f22,plain,(
% 2.10/0.63    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f19])).
% 2.10/0.63  fof(f19,negated_conjecture,(
% 2.10/0.63    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 2.10/0.63    inference(negated_conjecture,[],[f18])).
% 2.10/0.63  fof(f18,conjecture,(
% 2.10/0.63    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 2.10/0.63  fof(f66,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f39])).
% 2.10/0.63  fof(f39,plain,(
% 2.10/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.10/0.63    inference(flattening,[],[f38])).
% 2.10/0.63  fof(f38,plain,(
% 2.10/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.10/0.63    inference(ennf_transformation,[],[f11])).
% 2.10/0.63  fof(f11,axiom,(
% 2.10/0.63    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.10/0.63  fof(f542,plain,(
% 2.10/0.63    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 2.10/0.63    inference(subsumption_resolution,[],[f541,f42])).
% 2.10/0.63  fof(f541,plain,(
% 2.10/0.63    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 2.10/0.63    inference(superposition,[],[f56,f216])).
% 2.10/0.63  fof(f216,plain,(
% 2.10/0.63    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 2.10/0.63    inference(forward_demodulation,[],[f215,f163])).
% 2.10/0.63  fof(f163,plain,(
% 2.10/0.63    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0)) )),
% 2.10/0.63    inference(resolution,[],[f130,f81])).
% 2.10/0.63  fof(f81,plain,(
% 2.10/0.63    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | k1_xboole_0 = k3_xboole_0(X2,X3)) )),
% 2.10/0.63    inference(resolution,[],[f60,f59])).
% 2.10/0.63  fof(f59,plain,(
% 2.10/0.63    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 2.10/0.63    inference(cnf_transformation,[],[f34])).
% 2.10/0.63  fof(f34,plain,(
% 2.10/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.10/0.63    inference(ennf_transformation,[],[f6])).
% 2.10/0.63  fof(f6,axiom,(
% 2.10/0.63    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.10/0.63  fof(f60,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f35])).
% 2.10/0.63  fof(f35,plain,(
% 2.10/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.10/0.63    inference(ennf_transformation,[],[f20])).
% 2.10/0.63  fof(f20,plain,(
% 2.10/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.10/0.63    inference(rectify,[],[f5])).
% 2.10/0.63  fof(f5,axiom,(
% 2.10/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.10/0.63  fof(f130,plain,(
% 2.10/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.10/0.63    inference(resolution,[],[f84,f42])).
% 2.10/0.63  fof(f84,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~v1_xboole_0(X1) | r1_xboole_0(X0,X1)) )),
% 2.10/0.63    inference(resolution,[],[f64,f58])).
% 2.10/0.63  fof(f58,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f1])).
% 2.10/0.63  fof(f1,axiom,(
% 2.10/0.63    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.10/0.63  fof(f64,plain,(
% 2.10/0.63    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f36])).
% 2.10/0.63  fof(f36,plain,(
% 2.10/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.10/0.63    inference(ennf_transformation,[],[f21])).
% 2.10/0.63  fof(f21,plain,(
% 2.10/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.10/0.63    inference(rectify,[],[f4])).
% 2.10/0.63  fof(f4,axiom,(
% 2.10/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.10/0.63  fof(f215,plain,(
% 2.10/0.63    k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)),
% 2.10/0.63    inference(resolution,[],[f135,f65])).
% 2.10/0.63  fof(f65,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.10/0.63    inference(cnf_transformation,[],[f37])).
% 2.10/0.63  fof(f37,plain,(
% 2.10/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.10/0.63    inference(ennf_transformation,[],[f7])).
% 2.10/0.63  fof(f7,axiom,(
% 2.10/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.10/0.63  fof(f135,plain,(
% 2.10/0.63    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)),
% 2.10/0.63    inference(forward_demodulation,[],[f132,f44])).
% 2.10/0.63  fof(f44,plain,(
% 2.10/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.10/0.63    inference(cnf_transformation,[],[f17])).
% 2.10/0.63  fof(f17,axiom,(
% 2.10/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 2.10/0.63  fof(f132,plain,(
% 2.10/0.63    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0))),
% 2.10/0.63    inference(resolution,[],[f99,f71])).
% 2.10/0.63  fof(f99,plain,(
% 2.10/0.63    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(X0))) )),
% 2.10/0.63    inference(resolution,[],[f50,f41])).
% 2.10/0.63  fof(f50,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f29])).
% 2.10/0.63  fof(f29,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f14])).
% 2.10/0.63  fof(f14,axiom,(
% 2.10/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 2.10/0.63  fof(f56,plain,(
% 2.10/0.63    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f33])).
% 2.10/0.63  fof(f33,plain,(
% 2.10/0.63    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 2.10/0.63    inference(flattening,[],[f32])).
% 2.10/0.63  fof(f32,plain,(
% 2.10/0.63    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 2.10/0.63    inference(ennf_transformation,[],[f12])).
% 2.10/0.63  fof(f12,axiom,(
% 2.10/0.63    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 2.10/0.63  fof(f40,plain,(
% 2.10/0.63    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 2.10/0.63    inference(cnf_transformation,[],[f22])).
% 2.10/0.63  fof(f2275,plain,(
% 2.10/0.63    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 2.10/0.63    inference(forward_demodulation,[],[f2205,f721])).
% 2.10/0.63  fof(f721,plain,(
% 2.10/0.63    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 2.10/0.63    inference(subsumption_resolution,[],[f703,f701])).
% 2.10/0.63  fof(f701,plain,(
% 2.10/0.63    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) )),
% 2.10/0.63    inference(subsumption_resolution,[],[f700,f129])).
% 2.10/0.63  fof(f129,plain,(
% 2.10/0.63    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.10/0.63    inference(resolution,[],[f82,f42])).
% 2.10/0.63  fof(f82,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_xboole_0(X0,X1)) )),
% 2.10/0.63    inference(resolution,[],[f63,f58])).
% 2.10/0.63  fof(f63,plain,(
% 2.10/0.63    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f36])).
% 2.10/0.63  fof(f700,plain,(
% 2.10/0.63    ( ! [X4,X5] : (~r2_hidden(X5,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X4)) )),
% 2.10/0.63    inference(superposition,[],[f60,f137])).
% 2.10/0.63  fof(f137,plain,(
% 2.10/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.10/0.63    inference(resolution,[],[f81,f129])).
% 2.10/0.63  fof(f703,plain,(
% 2.10/0.63    r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 2.10/0.63    inference(subsumption_resolution,[],[f415,f701])).
% 2.10/0.63  fof(f415,plain,(
% 2.10/0.63    r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 2.10/0.63    inference(resolution,[],[f110,f71])).
% 2.10/0.63  fof(f110,plain,(
% 2.10/0.63    ( ! [X1] : (~v1_relat_1(X1) | r2_hidden(k4_tarski(sK4(k1_xboole_0,X1),sK3(k1_xboole_0,X1)),k1_xboole_0) | r2_hidden(k4_tarski(sK3(k1_xboole_0,X1),sK4(k1_xboole_0,X1)),X1) | k4_relat_1(k1_xboole_0) = X1) )),
% 2.10/0.63    inference(resolution,[],[f54,f71])).
% 2.10/0.63  fof(f54,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | k4_relat_1(X0) = X1) )),
% 2.10/0.63    inference(cnf_transformation,[],[f31])).
% 2.10/0.63  fof(f31,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f9])).
% 2.10/0.63  fof(f9,axiom,(
% 2.10/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).
% 2.10/0.63  fof(f2205,plain,(
% 2.10/0.63    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0)),
% 2.10/0.63    inference(backward_demodulation,[],[f265,f2202])).
% 2.10/0.63  fof(f2202,plain,(
% 2.10/0.63    k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 2.10/0.63    inference(resolution,[],[f2066,f46])).
% 2.10/0.63  fof(f2066,plain,(
% 2.10/0.63    v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 2.10/0.63    inference(subsumption_resolution,[],[f2065,f264])).
% 2.10/0.63  fof(f264,plain,(
% 2.10/0.63    v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 2.10/0.63    inference(resolution,[],[f257,f47])).
% 2.10/0.63  fof(f47,plain,(
% 2.10/0.63    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f25])).
% 2.10/0.63  fof(f25,plain,(
% 2.10/0.63    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f10])).
% 2.10/0.63  fof(f10,axiom,(
% 2.10/0.63    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 2.10/0.63  fof(f257,plain,(
% 2.10/0.63    v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 2.10/0.63    inference(resolution,[],[f87,f41])).
% 2.10/0.63  fof(f87,plain,(
% 2.10/0.63    ( ! [X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(k1_xboole_0,X1))) )),
% 2.10/0.63    inference(resolution,[],[f66,f71])).
% 2.10/0.63  fof(f2065,plain,(
% 2.10/0.63    ~v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 2.10/0.63    inference(subsumption_resolution,[],[f2064,f42])).
% 2.10/0.63  fof(f2064,plain,(
% 2.10/0.63    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 2.10/0.63    inference(superposition,[],[f56,f1016])).
% 2.10/0.63  fof(f1016,plain,(
% 2.10/0.63    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 2.10/0.63    inference(forward_demodulation,[],[f1015,f163])).
% 2.10/0.63  fof(f1015,plain,(
% 2.10/0.63    k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k3_xboole_0(k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0)),
% 2.10/0.63    inference(resolution,[],[f849,f65])).
% 2.10/0.63  fof(f849,plain,(
% 2.10/0.63    r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0)),
% 2.10/0.63    inference(backward_demodulation,[],[f289,f757])).
% 2.10/0.63  fof(f757,plain,(
% 2.10/0.63    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 2.10/0.63    inference(backward_demodulation,[],[f360,f721])).
% 2.10/0.63  fof(f360,plain,(
% 2.10/0.63    k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 2.10/0.63    inference(resolution,[],[f106,f41])).
% 2.10/0.63  fof(f106,plain,(
% 2.10/0.63    ( ! [X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(k1_xboole_0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(k1_xboole_0))) )),
% 2.10/0.63    inference(resolution,[],[f51,f71])).
% 2.10/0.63  fof(f51,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f30])).
% 2.10/0.63  fof(f30,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f15])).
% 2.10/0.63  fof(f15,axiom,(
% 2.10/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 2.10/0.63  fof(f289,plain,(
% 2.10/0.63    r1_tarski(k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),k1_xboole_0)),
% 2.10/0.63    inference(forward_demodulation,[],[f280,f44])).
% 2.10/0.63  fof(f280,plain,(
% 2.10/0.63    r1_tarski(k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),k2_relat_1(k1_xboole_0))),
% 2.10/0.63    inference(resolution,[],[f101,f71])).
% 2.10/0.63  fof(f101,plain,(
% 2.10/0.63    ( ! [X2] : (~v1_relat_1(X2) | r1_tarski(k2_relat_1(k5_relat_1(k4_relat_1(sK0),X2)),k2_relat_1(X2))) )),
% 2.10/0.63    inference(resolution,[],[f50,f73])).
% 2.10/0.63  fof(f73,plain,(
% 2.10/0.63    v1_relat_1(k4_relat_1(sK0))),
% 2.10/0.63    inference(resolution,[],[f47,f41])).
% 2.10/0.63  fof(f265,plain,(
% 2.10/0.63    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 2.10/0.63    inference(resolution,[],[f257,f48])).
% 2.10/0.63  fof(f48,plain,(
% 2.10/0.63    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 2.10/0.63    inference(cnf_transformation,[],[f26])).
% 2.10/0.63  fof(f26,plain,(
% 2.10/0.63    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f13])).
% 2.10/0.63  fof(f13,axiom,(
% 2.10/0.63    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 2.10/0.63  % SZS output end Proof for theBenchmark
% 2.10/0.63  % (12853)------------------------------
% 2.10/0.63  % (12853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.63  % (12853)Termination reason: Refutation
% 2.10/0.63  
% 2.10/0.63  % (12853)Memory used [KB]: 3965
% 2.10/0.63  % (12853)Time elapsed: 0.201 s
% 2.10/0.63  % (12853)------------------------------
% 2.10/0.63  % (12853)------------------------------
% 2.10/0.63  % (12835)Success in time 0.274 s
%------------------------------------------------------------------------------
