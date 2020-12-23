%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:35 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 360 expanded)
%              Number of leaves         :   23 ( 115 expanded)
%              Depth                    :   21
%              Number of atoms          :  253 ( 665 expanded)
%              Number of equality atoms :   67 ( 296 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1739,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f43,f91,f493])).

fof(f493,plain,(
    ! [X6,X5] :
      ( k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X6,X6,X6,X6,X6))) = X5
      | ~ r2_hidden(X6,X5) ) ),
    inference(forward_demodulation,[],[f488,f79])).

fof(f79,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f45,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f488,plain,(
    ! [X6,X5] :
      ( k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X6,X6,X6,X6,X6))) = k3_tarski(k3_enumset1(X5,X5,X5,X5,k1_xboole_0))
      | ~ r2_hidden(X6,X5) ) ),
    inference(backward_demodulation,[],[f321,f482])).

fof(f482,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f478,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f478,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f476,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f476,plain,(
    ! [X11] : k1_xboole_0 = k5_xboole_0(X11,k3_xboole_0(X11,X11)) ),
    inference(forward_demodulation,[],[f472,f125])).

fof(f125,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f79,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f50,f75,f75])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f472,plain,(
    ! [X11] : k1_xboole_0 = k5_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X11)),k3_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X11)),X11)) ),
    inference(resolution,[],[f169,f294])).

fof(f294,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f286,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f286,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f278,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f278,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f270,f229])).

fof(f229,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_xboole_0),X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f207,f47])).

fof(f207,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_xboole_0)
      | r2_hidden(sK2(k1_xboole_0),X0) ) ),
    inference(resolution,[],[f197,f48])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f193,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f89,f58])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f193,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f80,f125])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f270,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,sK2(k1_xboole_0))
      | ~ r2_hidden(X3,k1_xboole_0) ) ),
    inference(resolution,[],[f229,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f169,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X3),X2)
      | k5_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),k3_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X3)) = X2 ) ),
    inference(resolution,[],[f83,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = X0 ) ),
    inference(definition_unfolding,[],[f59,f53,f76])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f321,plain,(
    ! [X6,X5] :
      ( k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X6,X6,X6,X6,X6))) = k3_tarski(k3_enumset1(X5,X5,X5,X5,k5_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),k3_enumset1(X6,X6,X6,X6,X6))))
      | ~ r2_hidden(X6,X5) ) ),
    inference(resolution,[],[f157,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f75])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0))) ) ),
    inference(superposition,[],[f82,f58])).

fof(f82,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f54,f76,f53,f76])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f91,plain,(
    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f78,f81])).

fof(f78,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f44,f76,f77])).

fof(f44,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f43,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (810123264)
% 0.13/0.37  ipcrm: permission denied for id (810287113)
% 0.13/0.38  ipcrm: permission denied for id (810385425)
% 0.13/0.38  ipcrm: permission denied for id (810450963)
% 0.20/0.39  ipcrm: permission denied for id (810516510)
% 0.20/0.40  ipcrm: permission denied for id (810647591)
% 0.20/0.41  ipcrm: permission denied for id (810876974)
% 0.20/0.42  ipcrm: permission denied for id (810909745)
% 0.20/0.42  ipcrm: permission denied for id (810942514)
% 0.20/0.44  ipcrm: permission denied for id (811237445)
% 0.20/0.45  ipcrm: permission denied for id (811302993)
% 0.20/0.46  ipcrm: permission denied for id (811368531)
% 0.20/0.46  ipcrm: permission denied for id (811434071)
% 0.20/0.46  ipcrm: permission denied for id (811466841)
% 0.20/0.47  ipcrm: permission denied for id (811532380)
% 0.20/0.47  ipcrm: permission denied for id (811597922)
% 0.20/0.48  ipcrm: permission denied for id (811630692)
% 0.20/0.48  ipcrm: permission denied for id (811696231)
% 0.20/0.49  ipcrm: permission denied for id (811794543)
% 0.20/0.49  ipcrm: permission denied for id (811860085)
% 0.20/0.50  ipcrm: permission denied for id (811925623)
% 0.20/0.50  ipcrm: permission denied for id (811958392)
% 0.36/0.63  % (14788)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.36/0.63  % (14767)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.36/0.65  % (14774)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.36/0.65  % (14772)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.36/0.65  % (14782)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.36/0.66  % (14790)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.36/0.66  % (14765)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.36/0.66  % (14780)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.36/0.66  % (14784)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.36/0.66  % (14766)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.36/0.66  % (14766)Refutation not found, incomplete strategy% (14766)------------------------------
% 0.36/0.66  % (14766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.66  % (14766)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.66  
% 0.36/0.66  % (14766)Memory used [KB]: 1663
% 0.36/0.66  % (14766)Time elapsed: 0.101 s
% 0.36/0.66  % (14766)------------------------------
% 0.36/0.66  % (14766)------------------------------
% 0.36/0.66  % (14792)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.36/0.67  % (14779)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.36/0.67  % (14775)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.36/0.67  % (14769)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.36/0.67  % (14771)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.36/0.67  % (14779)Refutation not found, incomplete strategy% (14779)------------------------------
% 0.36/0.67  % (14779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.67  % (14779)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.67  
% 0.36/0.67  % (14779)Memory used [KB]: 1663
% 0.36/0.67  % (14779)Time elapsed: 0.113 s
% 0.36/0.67  % (14779)------------------------------
% 0.36/0.67  % (14779)------------------------------
% 0.36/0.67  % (14782)Refutation not found, incomplete strategy% (14782)------------------------------
% 0.36/0.67  % (14782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.67  % (14782)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.67  
% 0.36/0.67  % (14782)Memory used [KB]: 1663
% 0.36/0.67  % (14782)Time elapsed: 0.126 s
% 0.36/0.67  % (14782)------------------------------
% 0.36/0.67  % (14782)------------------------------
% 0.36/0.68  % (14776)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.36/0.68  % (14786)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.36/0.68  % (14768)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.36/0.68  % (14781)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.36/0.68  % (14794)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.36/0.68  % (14794)Refutation not found, incomplete strategy% (14794)------------------------------
% 0.36/0.68  % (14794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.68  % (14794)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.68  
% 0.36/0.68  % (14794)Memory used [KB]: 1663
% 0.36/0.68  % (14794)Time elapsed: 0.089 s
% 0.36/0.68  % (14794)------------------------------
% 0.36/0.68  % (14794)------------------------------
% 0.36/0.68  % (14773)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.36/0.69  % (14781)Refutation not found, incomplete strategy% (14781)------------------------------
% 0.36/0.69  % (14781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.69  % (14781)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.69  
% 0.36/0.69  % (14781)Memory used [KB]: 10618
% 0.36/0.69  % (14781)Time elapsed: 0.130 s
% 0.36/0.69  % (14781)------------------------------
% 0.36/0.69  % (14781)------------------------------
% 0.36/0.69  % (14775)Refutation not found, incomplete strategy% (14775)------------------------------
% 0.36/0.69  % (14775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.69  % (14775)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.69  
% 0.36/0.69  % (14775)Memory used [KB]: 10746
% 0.36/0.69  % (14775)Time elapsed: 0.130 s
% 0.36/0.69  % (14775)------------------------------
% 0.36/0.69  % (14775)------------------------------
% 0.36/0.69  % (14787)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.36/0.69  % (14785)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.36/0.69  % (14793)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.36/0.69  % (14789)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.36/0.69  % (14778)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.36/0.69  % (14770)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.58/0.70  % (14791)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.58/0.70  % (14783)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.58/0.70  % (14777)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.58/0.70  % (14777)Refutation not found, incomplete strategy% (14777)------------------------------
% 0.58/0.70  % (14777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.58/0.70  % (14793)Refutation not found, incomplete strategy% (14793)------------------------------
% 0.58/0.70  % (14793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.58/0.70  % (14777)Termination reason: Refutation not found, incomplete strategy
% 0.58/0.70  
% 0.58/0.70  % (14777)Memory used [KB]: 10618
% 0.58/0.70  % (14777)Time elapsed: 0.144 s
% 0.58/0.70  % (14777)------------------------------
% 0.58/0.70  % (14777)------------------------------
% 0.58/0.70  % (14793)Termination reason: Refutation not found, incomplete strategy
% 0.58/0.70  
% 0.58/0.70  % (14793)Memory used [KB]: 10746
% 0.58/0.70  % (14793)Time elapsed: 0.142 s
% 0.58/0.70  % (14793)------------------------------
% 0.58/0.70  % (14793)------------------------------
% 0.72/0.80  % (14780)Refutation not found, incomplete strategy% (14780)------------------------------
% 0.72/0.80  % (14780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.72/0.80  % (14780)Termination reason: Refutation not found, incomplete strategy
% 0.72/0.80  
% 0.72/0.80  % (14780)Memory used [KB]: 6140
% 0.72/0.80  % (14780)Time elapsed: 0.232 s
% 0.72/0.80  % (14780)------------------------------
% 0.72/0.80  % (14780)------------------------------
% 0.72/0.80  % (14765)Refutation not found, incomplete strategy% (14765)------------------------------
% 0.72/0.80  % (14765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.72/0.80  % (14765)Termination reason: Refutation not found, incomplete strategy
% 0.72/0.80  
% 0.72/0.80  % (14765)Memory used [KB]: 1663
% 0.72/0.80  % (14765)Time elapsed: 0.237 s
% 0.72/0.80  % (14765)------------------------------
% 0.72/0.80  % (14765)------------------------------
% 0.72/0.80  % (14797)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 0.72/0.80  % (14796)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 0.72/0.80  % (14802)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 0.72/0.80  % (14803)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 0.72/0.81  % (14798)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 0.72/0.81  % (14798)Refutation not found, incomplete strategy% (14798)------------------------------
% 0.72/0.81  % (14798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.72/0.81  % (14798)Termination reason: Refutation not found, incomplete strategy
% 0.72/0.81  
% 0.72/0.81  % (14798)Memory used [KB]: 6140
% 0.72/0.81  % (14798)Time elapsed: 0.105 s
% 0.72/0.81  % (14798)------------------------------
% 0.72/0.81  % (14798)------------------------------
% 0.72/0.83  % (14799)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 0.72/0.83  % (14800)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 0.72/0.83  % (14800)Refutation not found, incomplete strategy% (14800)------------------------------
% 0.72/0.83  % (14800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.72/0.83  % (14800)Termination reason: Refutation not found, incomplete strategy
% 0.72/0.83  
% 0.72/0.83  % (14800)Memory used [KB]: 10618
% 0.72/0.83  % (14800)Time elapsed: 0.114 s
% 0.72/0.83  % (14800)------------------------------
% 0.72/0.83  % (14800)------------------------------
% 0.72/0.83  % (14768)Refutation not found, incomplete strategy% (14768)------------------------------
% 0.72/0.83  % (14768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.72/0.83  % (14768)Termination reason: Refutation not found, incomplete strategy
% 0.72/0.83  
% 0.72/0.83  % (14768)Memory used [KB]: 6140
% 0.72/0.83  % (14768)Time elapsed: 0.271 s
% 0.72/0.83  % (14768)------------------------------
% 0.72/0.83  % (14768)------------------------------
% 1.04/0.84  % (14801)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.04/0.85  % (14787)Refutation found. Thanks to Tanya!
% 1.04/0.85  % SZS status Theorem for theBenchmark
% 1.04/0.85  % SZS output start Proof for theBenchmark
% 1.04/0.85  fof(f1739,plain,(
% 1.04/0.85    $false),
% 1.04/0.85    inference(unit_resulting_resolution,[],[f43,f91,f493])).
% 1.04/0.85  fof(f493,plain,(
% 1.04/0.85    ( ! [X6,X5] : (k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X6,X6,X6,X6,X6))) = X5 | ~r2_hidden(X6,X5)) )),
% 1.04/0.85    inference(forward_demodulation,[],[f488,f79])).
% 1.04/0.85  fof(f79,plain,(
% 1.04/0.85    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.04/0.85    inference(definition_unfolding,[],[f45,f76])).
% 1.04/0.85  fof(f76,plain,(
% 1.04/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.04/0.85    inference(definition_unfolding,[],[f52,f75])).
% 1.04/0.85  fof(f75,plain,(
% 1.04/0.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.04/0.85    inference(definition_unfolding,[],[f51,f74])).
% 1.04/0.85  fof(f74,plain,(
% 1.04/0.85    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.04/0.85    inference(definition_unfolding,[],[f66,f73])).
% 1.04/0.85  fof(f73,plain,(
% 1.04/0.85    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.04/0.85    inference(cnf_transformation,[],[f16])).
% 1.04/0.85  fof(f16,axiom,(
% 1.04/0.85    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.04/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.04/0.85  fof(f66,plain,(
% 1.04/0.85    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.04/0.85    inference(cnf_transformation,[],[f15])).
% 1.04/0.85  fof(f15,axiom,(
% 1.04/0.85    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.04/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.04/0.85  fof(f51,plain,(
% 1.04/0.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.04/0.85    inference(cnf_transformation,[],[f14])).
% 1.04/0.85  fof(f14,axiom,(
% 1.04/0.85    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.04/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.04/0.85  fof(f52,plain,(
% 1.04/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.04/0.85    inference(cnf_transformation,[],[f18])).
% 1.04/0.85  fof(f18,axiom,(
% 1.04/0.85    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.04/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.04/0.85  fof(f45,plain,(
% 1.04/0.85    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.04/0.85    inference(cnf_transformation,[],[f7])).
% 1.04/0.85  fof(f7,axiom,(
% 1.04/0.85    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.04/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.04/0.85  fof(f488,plain,(
% 1.04/0.85    ( ! [X6,X5] : (k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X6,X6,X6,X6,X6))) = k3_tarski(k3_enumset1(X5,X5,X5,X5,k1_xboole_0)) | ~r2_hidden(X6,X5)) )),
% 1.04/0.85    inference(backward_demodulation,[],[f321,f482])).
% 1.04/0.85  fof(f482,plain,(
% 1.04/0.85    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.04/0.85    inference(subsumption_resolution,[],[f478,f86])).
% 1.04/0.85  fof(f86,plain,(
% 1.04/0.85    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.04/0.85    inference(equality_resolution,[],[f62])).
% 1.04/0.85  fof(f62,plain,(
% 1.04/0.85    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.04/0.85    inference(cnf_transformation,[],[f36])).
% 1.04/0.85  fof(f36,plain,(
% 1.04/0.85    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.04/0.85    inference(flattening,[],[f35])).
% 1.04/0.85  fof(f35,plain,(
% 1.04/0.85    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.04/0.85    inference(nnf_transformation,[],[f5])).
% 1.04/0.85  fof(f5,axiom,(
% 1.04/0.85    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.04/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.04/0.85  fof(f478,plain,(
% 1.04/0.85    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 1.04/0.85    inference(superposition,[],[f476,f58])).
% 1.04/0.85  fof(f58,plain,(
% 1.04/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.04/0.85    inference(cnf_transformation,[],[f24])).
% 1.04/0.85  fof(f24,plain,(
% 1.04/0.85    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.04/0.85    inference(ennf_transformation,[],[f8])).
% 1.04/0.85  fof(f8,axiom,(
% 1.04/0.85    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.04/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.04/0.85  fof(f476,plain,(
% 1.04/0.85    ( ! [X11] : (k1_xboole_0 = k5_xboole_0(X11,k3_xboole_0(X11,X11))) )),
% 1.04/0.85    inference(forward_demodulation,[],[f472,f125])).
% 1.04/0.85  fof(f125,plain,(
% 1.04/0.85    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.04/0.85    inference(superposition,[],[f79,f81])).
% 1.04/0.85  fof(f81,plain,(
% 1.04/0.85    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.04/0.85    inference(definition_unfolding,[],[f50,f75,f75])).
% 1.04/0.85  fof(f50,plain,(
% 1.04/0.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.04/0.85    inference(cnf_transformation,[],[f12])).
% 1.04/0.85  fof(f12,axiom,(
% 1.04/0.85    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.04/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.04/0.85  fof(f472,plain,(
% 1.04/0.85    ( ! [X11] : (k1_xboole_0 = k5_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X11)),k3_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X11)),X11))) )),
% 1.04/0.85    inference(resolution,[],[f169,f294])).
% 1.04/0.85  fof(f294,plain,(
% 1.04/0.85    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.04/0.85    inference(subsumption_resolution,[],[f286,f47])).
% 1.04/0.85  fof(f47,plain,(
% 1.04/0.85    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.04/0.85    inference(cnf_transformation,[],[f32])).
% 1.04/0.85  fof(f32,plain,(
% 1.04/0.85    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.04/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 1.04/0.85  fof(f31,plain,(
% 1.04/0.85    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.04/0.85    introduced(choice_axiom,[])).
% 1.04/0.85  fof(f30,plain,(
% 1.04/0.85    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.04/0.85    inference(rectify,[],[f29])).
% 1.04/0.85  fof(f29,plain,(
% 1.04/0.85    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.04/0.85    inference(nnf_transformation,[],[f2])).
% 1.04/0.85  fof(f2,axiom,(
% 1.04/0.85    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.04/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.04/0.85  fof(f286,plain,(
% 1.04/0.85    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | v1_xboole_0(k1_xboole_0)) )),
% 1.04/0.85    inference(resolution,[],[f278,f48])).
% 1.04/0.85  fof(f48,plain,(
% 1.04/0.85    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 1.04/0.85    inference(cnf_transformation,[],[f32])).
% 1.04/0.85  fof(f278,plain,(
% 1.04/0.85    ( ! [X2,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X2,k1_xboole_0)) )),
% 1.04/0.85    inference(resolution,[],[f270,f229])).
% 1.04/0.85  fof(f229,plain,(
% 1.04/0.85    ( ! [X0,X1] : (r2_hidden(sK2(k1_xboole_0),X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.04/0.85    inference(resolution,[],[f207,f47])).
% 1.04/0.85  fof(f207,plain,(
% 1.04/0.85    ( ! [X0] : (v1_xboole_0(k1_xboole_0) | r2_hidden(sK2(k1_xboole_0),X0)) )),
% 1.04/0.85    inference(resolution,[],[f197,f48])).
% 1.04/0.85  fof(f197,plain,(
% 1.04/0.85    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 1.04/0.85    inference(resolution,[],[f193,f95])).
% 1.04/0.85  fof(f95,plain,(
% 1.04/0.85    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.04/0.85    inference(superposition,[],[f89,f58])).
% 1.04/0.85  fof(f89,plain,(
% 1.04/0.85    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 1.04/0.85    inference(equality_resolution,[],[f68])).
% 1.04/0.85  fof(f68,plain,(
% 1.04/0.85    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.04/0.85    inference(cnf_transformation,[],[f42])).
% 1.04/0.85  fof(f42,plain,(
% 1.04/0.85    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.04/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.04/0.87  fof(f41,plain,(
% 1.04/0.87    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.04/0.87    introduced(choice_axiom,[])).
% 1.04/0.87  fof(f40,plain,(
% 1.04/0.87    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.04/0.87    inference(rectify,[],[f39])).
% 1.04/0.87  fof(f39,plain,(
% 1.04/0.87    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.04/0.87    inference(flattening,[],[f38])).
% 1.04/0.87  fof(f38,plain,(
% 1.04/0.87    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.04/0.87    inference(nnf_transformation,[],[f3])).
% 1.04/0.87  fof(f3,axiom,(
% 1.04/0.87    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.04/0.87  fof(f193,plain,(
% 1.04/0.87    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.04/0.87    inference(superposition,[],[f80,f125])).
% 1.04/0.87  fof(f80,plain,(
% 1.04/0.87    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.04/0.87    inference(definition_unfolding,[],[f49,f76])).
% 1.04/0.87  fof(f49,plain,(
% 1.04/0.87    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.04/0.87    inference(cnf_transformation,[],[f10])).
% 1.04/0.87  fof(f10,axiom,(
% 1.04/0.87    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.04/0.87  fof(f270,plain,(
% 1.04/0.87    ( ! [X4,X3] : (~r2_hidden(X4,sK2(k1_xboole_0)) | ~r2_hidden(X3,k1_xboole_0)) )),
% 1.04/0.87    inference(resolution,[],[f229,f60])).
% 1.04/0.87  fof(f60,plain,(
% 1.04/0.87    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.04/0.87    inference(cnf_transformation,[],[f26])).
% 1.04/0.87  fof(f26,plain,(
% 1.04/0.87    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.04/0.87    inference(ennf_transformation,[],[f1])).
% 1.04/0.87  fof(f1,axiom,(
% 1.04/0.87    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.04/0.87  fof(f169,plain,(
% 1.04/0.87    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3),X2) | k5_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),k3_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X3)) = X2) )),
% 1.04/0.87    inference(resolution,[],[f83,f55])).
% 1.04/0.87  fof(f55,plain,(
% 1.04/0.87    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.04/0.87    inference(cnf_transformation,[],[f34])).
% 1.04/0.87  fof(f34,plain,(
% 1.04/0.87    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.04/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f33])).
% 1.04/0.87  fof(f33,plain,(
% 1.04/0.87    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.04/0.87    introduced(choice_axiom,[])).
% 1.04/0.87  fof(f23,plain,(
% 1.04/0.87    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.04/0.87    inference(ennf_transformation,[],[f21])).
% 1.04/0.87  fof(f21,plain,(
% 1.04/0.87    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.04/0.87    inference(rectify,[],[f4])).
% 1.04/0.87  fof(f4,axiom,(
% 1.04/0.87    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.04/0.87  fof(f83,plain,(
% 1.04/0.87    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = X0) )),
% 1.04/0.87    inference(definition_unfolding,[],[f59,f53,f76])).
% 1.04/0.87  fof(f53,plain,(
% 1.04/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.04/0.87    inference(cnf_transformation,[],[f6])).
% 1.04/0.87  fof(f6,axiom,(
% 1.04/0.87    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.04/0.87  fof(f59,plain,(
% 1.04/0.87    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.04/0.87    inference(cnf_transformation,[],[f25])).
% 1.04/0.87  fof(f25,plain,(
% 1.04/0.87    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.04/0.87    inference(ennf_transformation,[],[f11])).
% 1.04/0.87  fof(f11,axiom,(
% 1.04/0.87    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 1.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 1.04/0.87  fof(f321,plain,(
% 1.04/0.87    ( ! [X6,X5] : (k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X6,X6,X6,X6,X6))) = k3_tarski(k3_enumset1(X5,X5,X5,X5,k5_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),k3_enumset1(X6,X6,X6,X6,X6)))) | ~r2_hidden(X6,X5)) )),
% 1.04/0.87    inference(resolution,[],[f157,f84])).
% 1.04/0.87  fof(f84,plain,(
% 1.04/0.87    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.04/0.87    inference(definition_unfolding,[],[f65,f77])).
% 1.04/0.87  fof(f77,plain,(
% 1.04/0.87    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.04/0.87    inference(definition_unfolding,[],[f46,f75])).
% 1.04/0.87  fof(f46,plain,(
% 1.04/0.87    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.04/0.87    inference(cnf_transformation,[],[f13])).
% 1.04/0.87  fof(f13,axiom,(
% 1.04/0.87    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.04/0.87  fof(f65,plain,(
% 1.04/0.87    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.04/0.87    inference(cnf_transformation,[],[f37])).
% 1.04/0.87  fof(f37,plain,(
% 1.04/0.87    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.04/0.87    inference(nnf_transformation,[],[f17])).
% 1.04/0.87  fof(f17,axiom,(
% 1.04/0.87    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.04/0.87  fof(f157,plain,(
% 1.04/0.87    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0)))) )),
% 1.04/0.87    inference(superposition,[],[f82,f58])).
% 1.04/0.87  fof(f82,plain,(
% 1.04/0.87    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.04/0.87    inference(definition_unfolding,[],[f54,f76,f53,f76])).
% 1.04/0.87  fof(f54,plain,(
% 1.04/0.87    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.04/0.87    inference(cnf_transformation,[],[f9])).
% 1.04/0.87  fof(f9,axiom,(
% 1.04/0.87    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.04/0.87  fof(f91,plain,(
% 1.04/0.87    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.04/0.87    inference(backward_demodulation,[],[f78,f81])).
% 1.04/0.87  fof(f78,plain,(
% 1.04/0.87    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.04/0.87    inference(definition_unfolding,[],[f44,f76,f77])).
% 1.04/0.87  fof(f44,plain,(
% 1.04/0.87    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.04/0.87    inference(cnf_transformation,[],[f28])).
% 1.04/0.87  fof(f28,plain,(
% 1.04/0.87    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 1.04/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f27])).
% 1.04/0.87  fof(f27,plain,(
% 1.04/0.87    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 1.04/0.87    introduced(choice_axiom,[])).
% 1.04/0.87  fof(f22,plain,(
% 1.04/0.87    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.04/0.87    inference(ennf_transformation,[],[f20])).
% 1.04/0.87  fof(f20,negated_conjecture,(
% 1.04/0.87    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.04/0.87    inference(negated_conjecture,[],[f19])).
% 1.04/0.87  fof(f19,conjecture,(
% 1.04/0.87    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.04/0.87  fof(f43,plain,(
% 1.04/0.87    r2_hidden(sK0,sK1)),
% 1.04/0.87    inference(cnf_transformation,[],[f28])).
% 1.04/0.87  % SZS output end Proof for theBenchmark
% 1.04/0.87  % (14787)------------------------------
% 1.04/0.87  % (14787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.04/0.87  % (14787)Termination reason: Refutation
% 1.04/0.87  
% 1.04/0.87  % (14787)Memory used [KB]: 7803
% 1.04/0.87  % (14787)Time elapsed: 0.265 s
% 1.04/0.87  % (14787)------------------------------
% 1.04/0.87  % (14787)------------------------------
% 1.04/0.87  % (14631)Success in time 0.508 s
%------------------------------------------------------------------------------
