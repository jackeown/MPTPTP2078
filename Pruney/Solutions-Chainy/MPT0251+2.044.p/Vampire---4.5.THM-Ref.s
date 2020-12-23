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
% DateTime   : Thu Dec  3 12:38:41 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 155 expanded)
%              Number of leaves         :   19 (  41 expanded)
%              Depth                    :   18
%              Number of atoms          :  241 ( 600 expanded)
%              Number of equality atoms :   58 ( 104 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1320,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1318,f43])).

fof(f43,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f1318,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f1316,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1316,plain,(
    ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(trivial_inequality_removal,[],[f1315])).

fof(f1315,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f100,f1172])).

fof(f1172,plain,(
    ! [X4,X3] :
      ( k2_xboole_0(X4,X3) = X4
      | ~ r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f1140,f47])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1140,plain,(
    ! [X4,X3] :
      ( k2_xboole_0(X4,X3) = k2_xboole_0(X4,k1_xboole_0)
      | ~ r1_tarski(X3,X4) ) ),
    inference(backward_demodulation,[],[f214,f1132])).

fof(f1132,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    inference(resolution,[],[f1075,f1014])).

fof(f1014,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f678,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f678,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X2,X3)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f521,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f521,plain,(
    ! [X54,X53] :
      ( k1_xboole_0 = k3_xboole_0(X53,X54)
      | ~ r1_xboole_0(X53,X54) ) ),
    inference(forward_demodulation,[],[f515,f261])).

fof(f261,plain,(
    ! [X25] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X25) ),
    inference(resolution,[],[f176,f195])).

fof(f195,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f185,f46])).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_xboole_0,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f88,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f57,f58])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f176,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f515,plain,(
    ! [X54,X55,X53] :
      ( k3_xboole_0(X53,X54) = k3_xboole_0(k1_xboole_0,X55)
      | ~ r1_xboole_0(X53,X54) ) ),
    inference(resolution,[],[f172,f195])).

fof(f172,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(sK3(X8,X9,k3_xboole_0(X10,X11)),X8)
      | k3_xboole_0(X10,X11) = k3_xboole_0(X8,X9)
      | ~ r1_xboole_0(X10,X11) ) ),
    inference(resolution,[],[f69,f57])).

fof(f1075,plain,(
    ! [X8,X9] : r1_xboole_0(k5_xboole_0(X8,X8),X9) ),
    inference(resolution,[],[f1070,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f56,f81])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1070,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k5_xboole_0(X1,X1)) ),
    inference(subsumption_resolution,[],[f1061,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f1061,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X1))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f460,f81])).

fof(f460,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k3_xboole_0(X0,X0))
      | ~ r2_hidden(X1,k5_xboole_0(X0,X0)) ) ),
    inference(subsumption_resolution,[],[f454,f73])).

fof(f454,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r2_hidden(X1,k3_xboole_0(X0,X0))
      | ~ r2_hidden(X1,k5_xboole_0(X0,X0)) ) ),
    inference(superposition,[],[f143,f49])).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f143,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X5,k2_xboole_0(X3,X4))
      | r2_hidden(X5,k3_xboole_0(X3,X4))
      | ~ r2_hidden(X5,k5_xboole_0(X3,X4)) ) ),
    inference(superposition,[],[f74,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f214,plain,(
    ! [X4,X3] :
      ( k2_xboole_0(X4,X3) = k2_xboole_0(X4,k5_xboole_0(X3,X3))
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f54,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f53,f58])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f100,plain,(
    sK1 != k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f44,f94])).

fof(f94,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f85,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f85,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f44,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.21/0.52  % (32084)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.21/0.53  % (32068)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.21/0.53  % (32058)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.21/0.53  % (32056)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.21/0.54  % (32060)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.21/0.54  % (32067)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.21/0.54  % (32057)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.21/0.54  % (32081)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.21/0.54  % (32059)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.42/0.54  % (32085)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.54  % (32084)Refutation not found, incomplete strategy% (32084)------------------------------
% 1.42/0.54  % (32084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (32084)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (32084)Memory used [KB]: 10746
% 1.42/0.54  % (32084)Time elapsed: 0.122 s
% 1.42/0.54  % (32084)------------------------------
% 1.42/0.54  % (32084)------------------------------
% 1.42/0.54  % (32074)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.54  % (32082)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.42/0.54  % (32073)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.54  % (32073)Refutation not found, incomplete strategy% (32073)------------------------------
% 1.42/0.54  % (32073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (32073)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (32073)Memory used [KB]: 1663
% 1.42/0.54  % (32073)Time elapsed: 0.132 s
% 1.42/0.54  % (32073)------------------------------
% 1.42/0.54  % (32073)------------------------------
% 1.42/0.54  % (32070)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.42/0.54  % (32077)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.54  % (32070)Refutation not found, incomplete strategy% (32070)------------------------------
% 1.42/0.54  % (32070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (32070)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (32070)Memory used [KB]: 1663
% 1.42/0.54  % (32070)Time elapsed: 0.104 s
% 1.42/0.54  % (32070)------------------------------
% 1.42/0.54  % (32070)------------------------------
% 1.42/0.55  % (32064)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.55  % (32079)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.42/0.55  % (32080)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.55  % (32062)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (32071)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.42/0.55  % (32078)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.42/0.55  % (32069)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.42/0.55  % (32075)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.55  % (32063)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.42/0.56  % (32065)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.56  % (32076)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.56  % (32066)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.56  % (32066)Refutation not found, incomplete strategy% (32066)------------------------------
% 1.42/0.56  % (32066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (32066)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (32066)Memory used [KB]: 10746
% 1.42/0.56  % (32066)Time elapsed: 0.156 s
% 1.42/0.56  % (32066)------------------------------
% 1.42/0.56  % (32066)------------------------------
% 1.42/0.56  % (32072)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.56  % (32072)Refutation not found, incomplete strategy% (32072)------------------------------
% 1.42/0.56  % (32072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (32072)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (32072)Memory used [KB]: 10618
% 1.42/0.56  % (32072)Time elapsed: 0.157 s
% 1.42/0.56  % (32072)------------------------------
% 1.42/0.56  % (32072)------------------------------
% 1.42/0.56  % (32061)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.42/0.56  % (32083)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.04/0.66  % (32065)Refutation found. Thanks to Tanya!
% 2.04/0.66  % SZS status Theorem for theBenchmark
% 2.04/0.67  % (32108)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.04/0.68  % SZS output start Proof for theBenchmark
% 2.04/0.68  fof(f1320,plain,(
% 2.04/0.68    $false),
% 2.04/0.68    inference(subsumption_resolution,[],[f1318,f43])).
% 2.04/0.68  fof(f43,plain,(
% 2.04/0.68    r2_hidden(sK0,sK1)),
% 2.04/0.68    inference(cnf_transformation,[],[f31])).
% 2.04/0.68  fof(f31,plain,(
% 2.04/0.68    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 2.04/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f30])).
% 2.04/0.68  fof(f30,plain,(
% 2.04/0.68    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 2.04/0.68    introduced(choice_axiom,[])).
% 2.04/0.68  fof(f25,plain,(
% 2.04/0.68    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 2.04/0.68    inference(ennf_transformation,[],[f22])).
% 2.04/0.68  fof(f22,negated_conjecture,(
% 2.04/0.68    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 2.04/0.68    inference(negated_conjecture,[],[f21])).
% 2.04/0.68  fof(f21,conjecture,(
% 2.04/0.68    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 2.04/0.68  fof(f1318,plain,(
% 2.04/0.68    ~r2_hidden(sK0,sK1)),
% 2.04/0.68    inference(resolution,[],[f1316,f64])).
% 2.04/0.68  fof(f64,plain,(
% 2.04/0.68    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f36])).
% 2.04/0.68  fof(f36,plain,(
% 2.04/0.68    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.04/0.68    inference(nnf_transformation,[],[f19])).
% 2.04/0.68  fof(f19,axiom,(
% 2.04/0.68    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.04/0.68  fof(f1316,plain,(
% 2.04/0.68    ~r1_tarski(k1_tarski(sK0),sK1)),
% 2.04/0.68    inference(trivial_inequality_removal,[],[f1315])).
% 2.04/0.68  fof(f1315,plain,(
% 2.04/0.68    sK1 != sK1 | ~r1_tarski(k1_tarski(sK0),sK1)),
% 2.04/0.68    inference(superposition,[],[f100,f1172])).
% 2.04/0.68  fof(f1172,plain,(
% 2.04/0.68    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = X4 | ~r1_tarski(X3,X4)) )),
% 2.04/0.68    inference(forward_demodulation,[],[f1140,f47])).
% 2.04/0.68  fof(f47,plain,(
% 2.04/0.68    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.04/0.68    inference(cnf_transformation,[],[f8])).
% 2.04/0.68  fof(f8,axiom,(
% 2.04/0.68    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.04/0.68  fof(f1140,plain,(
% 2.04/0.68    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k2_xboole_0(X4,k1_xboole_0) | ~r1_tarski(X3,X4)) )),
% 2.04/0.68    inference(backward_demodulation,[],[f214,f1132])).
% 2.04/0.68  fof(f1132,plain,(
% 2.04/0.68    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) )),
% 2.04/0.68    inference(resolution,[],[f1075,f1014])).
% 2.04/0.68  fof(f1014,plain,(
% 2.04/0.68    ( ! [X1] : (~r1_xboole_0(X1,X1) | k1_xboole_0 = X1) )),
% 2.04/0.68    inference(resolution,[],[f678,f77])).
% 2.04/0.68  fof(f77,plain,(
% 2.04/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.04/0.68    inference(equality_resolution,[],[f61])).
% 2.04/0.68  fof(f61,plain,(
% 2.04/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.04/0.68    inference(cnf_transformation,[],[f35])).
% 2.04/0.68  fof(f35,plain,(
% 2.04/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.68    inference(flattening,[],[f34])).
% 2.04/0.68  fof(f34,plain,(
% 2.04/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.68    inference(nnf_transformation,[],[f6])).
% 2.04/0.68  fof(f6,axiom,(
% 2.04/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.04/0.68  fof(f678,plain,(
% 2.04/0.68    ( ! [X2,X3] : (~r1_tarski(X2,X3) | ~r1_xboole_0(X2,X3) | k1_xboole_0 = X2) )),
% 2.04/0.68    inference(superposition,[],[f521,f58])).
% 2.04/0.68  fof(f58,plain,(
% 2.04/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f27])).
% 2.04/0.68  fof(f27,plain,(
% 2.04/0.68    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.04/0.68    inference(ennf_transformation,[],[f9])).
% 2.04/0.68  fof(f9,axiom,(
% 2.04/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.04/0.68  fof(f521,plain,(
% 2.04/0.68    ( ! [X54,X53] : (k1_xboole_0 = k3_xboole_0(X53,X54) | ~r1_xboole_0(X53,X54)) )),
% 2.04/0.68    inference(forward_demodulation,[],[f515,f261])).
% 2.04/0.68  fof(f261,plain,(
% 2.04/0.68    ( ! [X25] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X25)) )),
% 2.04/0.68    inference(resolution,[],[f176,f195])).
% 2.04/0.68  fof(f195,plain,(
% 2.04/0.68    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.04/0.68    inference(resolution,[],[f185,f46])).
% 2.04/0.68  fof(f46,plain,(
% 2.04/0.68    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f12])).
% 2.04/0.68  fof(f12,axiom,(
% 2.04/0.68    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.04/0.68  fof(f185,plain,(
% 2.04/0.68    ( ! [X0,X1] : (~r1_xboole_0(k1_xboole_0,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 2.04/0.68    inference(resolution,[],[f88,f45])).
% 2.04/0.68  fof(f45,plain,(
% 2.04/0.68    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f10])).
% 2.04/0.68  fof(f10,axiom,(
% 2.04/0.68    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.04/0.68  fof(f88,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 2.04/0.68    inference(superposition,[],[f57,f58])).
% 2.04/0.68  fof(f57,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f33])).
% 2.04/0.68  fof(f33,plain,(
% 2.04/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.04/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f32])).
% 2.04/0.68  fof(f32,plain,(
% 2.04/0.68    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 2.04/0.68    introduced(choice_axiom,[])).
% 2.04/0.68  fof(f26,plain,(
% 2.04/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.04/0.68    inference(ennf_transformation,[],[f24])).
% 2.04/0.68  fof(f24,plain,(
% 2.04/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.04/0.68    inference(rectify,[],[f5])).
% 2.04/0.68  fof(f5,axiom,(
% 2.04/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.04/0.68  fof(f176,plain,(
% 2.04/0.68    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) )),
% 2.04/0.68    inference(factoring,[],[f69])).
% 2.04/0.68  fof(f69,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 2.04/0.68    inference(cnf_transformation,[],[f41])).
% 2.04/0.68  fof(f41,plain,(
% 2.04/0.68    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.04/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 2.04/0.68  fof(f40,plain,(
% 2.04/0.68    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.04/0.68    introduced(choice_axiom,[])).
% 2.04/0.68  fof(f39,plain,(
% 2.04/0.68    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.04/0.68    inference(rectify,[],[f38])).
% 2.04/0.68  fof(f38,plain,(
% 2.04/0.68    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.04/0.68    inference(flattening,[],[f37])).
% 2.04/0.68  fof(f37,plain,(
% 2.04/0.68    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.04/0.68    inference(nnf_transformation,[],[f1])).
% 2.04/0.68  fof(f1,axiom,(
% 2.04/0.68    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.04/0.68  fof(f515,plain,(
% 2.04/0.68    ( ! [X54,X55,X53] : (k3_xboole_0(X53,X54) = k3_xboole_0(k1_xboole_0,X55) | ~r1_xboole_0(X53,X54)) )),
% 2.04/0.68    inference(resolution,[],[f172,f195])).
% 2.04/0.68  fof(f172,plain,(
% 2.04/0.68    ( ! [X10,X8,X11,X9] : (r2_hidden(sK3(X8,X9,k3_xboole_0(X10,X11)),X8) | k3_xboole_0(X10,X11) = k3_xboole_0(X8,X9) | ~r1_xboole_0(X10,X11)) )),
% 2.04/0.68    inference(resolution,[],[f69,f57])).
% 2.04/0.68  fof(f1075,plain,(
% 2.04/0.68    ( ! [X8,X9] : (r1_xboole_0(k5_xboole_0(X8,X8),X9)) )),
% 2.04/0.68    inference(resolution,[],[f1070,f115])).
% 2.04/0.68  fof(f115,plain,(
% 2.04/0.68    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.04/0.68    inference(resolution,[],[f56,f81])).
% 2.04/0.68  fof(f81,plain,(
% 2.04/0.68    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 2.04/0.68    inference(equality_resolution,[],[f66])).
% 2.04/0.68  fof(f66,plain,(
% 2.04/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.04/0.68    inference(cnf_transformation,[],[f41])).
% 2.04/0.68  fof(f56,plain,(
% 2.04/0.68    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f33])).
% 2.04/0.68  fof(f1070,plain,(
% 2.04/0.68    ( ! [X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X1))) )),
% 2.04/0.68    inference(subsumption_resolution,[],[f1061,f73])).
% 2.04/0.68  fof(f73,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f42])).
% 2.04/0.68  fof(f42,plain,(
% 2.04/0.68    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.04/0.68    inference(nnf_transformation,[],[f29])).
% 2.04/0.68  fof(f29,plain,(
% 2.04/0.68    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.04/0.68    inference(ennf_transformation,[],[f4])).
% 2.04/0.68  fof(f4,axiom,(
% 2.04/0.68    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.04/0.68  fof(f1061,plain,(
% 2.04/0.68    ( ! [X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X1)) | r2_hidden(X0,X1)) )),
% 2.04/0.68    inference(resolution,[],[f460,f81])).
% 2.04/0.68  fof(f460,plain,(
% 2.04/0.68    ( ! [X0,X1] : (r2_hidden(X1,k3_xboole_0(X0,X0)) | ~r2_hidden(X1,k5_xboole_0(X0,X0))) )),
% 2.04/0.68    inference(subsumption_resolution,[],[f454,f73])).
% 2.04/0.68  fof(f454,plain,(
% 2.04/0.68    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X1,k3_xboole_0(X0,X0)) | ~r2_hidden(X1,k5_xboole_0(X0,X0))) )),
% 2.04/0.68    inference(superposition,[],[f143,f49])).
% 2.04/0.68  fof(f49,plain,(
% 2.04/0.68    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.04/0.68    inference(cnf_transformation,[],[f23])).
% 2.04/0.68  fof(f23,plain,(
% 2.04/0.68    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.04/0.68    inference(rectify,[],[f2])).
% 2.04/0.68  fof(f2,axiom,(
% 2.04/0.68    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.04/0.68  fof(f143,plain,(
% 2.04/0.68    ( ! [X4,X5,X3] : (r2_hidden(X5,k2_xboole_0(X3,X4)) | r2_hidden(X5,k3_xboole_0(X3,X4)) | ~r2_hidden(X5,k5_xboole_0(X3,X4))) )),
% 2.04/0.68    inference(superposition,[],[f74,f55])).
% 2.04/0.68  fof(f55,plain,(
% 2.04/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.04/0.68    inference(cnf_transformation,[],[f13])).
% 2.04/0.68  fof(f13,axiom,(
% 2.04/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.04/0.68  fof(f74,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f42])).
% 2.04/0.68  fof(f214,plain,(
% 2.04/0.68    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k2_xboole_0(X4,k5_xboole_0(X3,X3)) | ~r1_tarski(X3,X4)) )),
% 2.04/0.68    inference(superposition,[],[f54,f97])).
% 2.04/0.68  fof(f97,plain,(
% 2.04/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) )),
% 2.04/0.68    inference(superposition,[],[f53,f58])).
% 2.04/0.68  fof(f53,plain,(
% 2.04/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.04/0.68    inference(cnf_transformation,[],[f7])).
% 2.04/0.68  fof(f7,axiom,(
% 2.04/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.04/0.68  fof(f54,plain,(
% 2.04/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f11])).
% 2.04/0.68  fof(f11,axiom,(
% 2.04/0.68    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.04/0.68  fof(f100,plain,(
% 2.04/0.68    sK1 != k2_xboole_0(sK1,k1_tarski(sK0))),
% 2.04/0.68    inference(superposition,[],[f44,f94])).
% 2.04/0.68  fof(f94,plain,(
% 2.04/0.68    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 2.04/0.68    inference(superposition,[],[f85,f52])).
% 2.04/0.68  fof(f52,plain,(
% 2.04/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.04/0.68    inference(cnf_transformation,[],[f20])).
% 2.04/0.68  fof(f20,axiom,(
% 2.04/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.04/0.68  fof(f85,plain,(
% 2.04/0.68    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 2.04/0.68    inference(superposition,[],[f52,f50])).
% 2.04/0.68  fof(f50,plain,(
% 2.04/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f14])).
% 2.04/0.68  fof(f14,axiom,(
% 2.04/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.04/0.68  fof(f44,plain,(
% 2.04/0.68    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 2.04/0.68    inference(cnf_transformation,[],[f31])).
% 2.04/0.68  % SZS output end Proof for theBenchmark
% 2.04/0.68  % (32065)------------------------------
% 2.04/0.68  % (32065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.68  % (32065)Termination reason: Refutation
% 2.04/0.68  
% 2.04/0.68  % (32065)Memory used [KB]: 2558
% 2.04/0.68  % (32065)Time elapsed: 0.256 s
% 2.04/0.68  % (32065)------------------------------
% 2.04/0.68  % (32065)------------------------------
% 2.04/0.68  % (32055)Success in time 0.318 s
%------------------------------------------------------------------------------
