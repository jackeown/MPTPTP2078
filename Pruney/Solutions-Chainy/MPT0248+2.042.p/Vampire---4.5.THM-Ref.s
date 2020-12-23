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
% DateTime   : Thu Dec  3 12:37:55 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  120 (5374 expanded)
%              Number of leaves         :   21 (1465 expanded)
%              Depth                    :   34
%              Number of atoms          :  269 (20057 expanded)
%              Number of equality atoms :  123 (12756 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2144,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2142,f2023])).

fof(f2023,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f1996,f282])).

fof(f282,plain,(
    k1_xboole_0 != sK2 ),
    inference(trivial_inequality_removal,[],[f278])).

fof(f278,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2 ),
    inference(superposition,[],[f59,f233])).

fof(f233,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f231,f163])).

fof(f163,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f160,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f160,plain,
    ( v1_xboole_0(sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f156,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f156,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK1 = k1_tarski(sK0) ) ),
    inference(forward_demodulation,[],[f155,f105])).

fof(f105,plain,(
    sK1 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f101,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f101,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f67,f56])).

fof(f56,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f155,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK1,k1_tarski(sK0)))
      | sK1 = k1_tarski(sK0) ) ),
    inference(forward_demodulation,[],[f154,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f154,plain,(
    ! [X0] :
      ( sK1 = k1_tarski(sK0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_tarski(sK0),sK1)) ) ),
    inference(resolution,[],[f146,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f146,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f141,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f141,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f103,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f103,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f101,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f231,plain,
    ( k1_xboole_0 != sK1
    | sK1 = k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f209])).

fof(f209,plain,
    ( sK2 != sK2
    | k1_xboole_0 != sK1
    | sK1 = k1_tarski(sK0) ),
    inference(superposition,[],[f58,f169])).

fof(f169,plain,
    ( sK2 = k1_tarski(sK0)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f161,f98])).

fof(f98,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK2 = k1_tarski(sK0) ),
    inference(superposition,[],[f56,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f161,plain,(
    ! [X4] :
      ( r1_tarski(sK1,X4)
      | sK1 = k1_tarski(sK0) ) ),
    inference(resolution,[],[f156,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f58,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f1996,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(sK2,sK1) ),
    inference(superposition,[],[f1975,f78])).

fof(f1975,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f1570,f362])).

fof(f362,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f280,f266])).

fof(f266,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f237,f265])).

fof(f265,plain,(
    sK1 != sK2 ),
    inference(forward_demodulation,[],[f264,f233])).

fof(f264,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f235])).

fof(f235,plain,
    ( sK1 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f57,f233])).

fof(f57,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f237,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f98,f233])).

fof(f280,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(superposition,[],[f88,f233])).

fof(f1570,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | k1_xboole_0 = k3_xboole_0(X0,sK1) ) ),
    inference(resolution,[],[f1564,f63])).

fof(f1564,plain,(
    ! [X5] :
      ( v1_xboole_0(k3_xboole_0(X5,sK1))
      | r2_hidden(sK0,X5) ) ),
    inference(superposition,[],[f1525,f69])).

fof(f1525,plain,(
    ! [X15] :
      ( v1_xboole_0(k3_xboole_0(sK1,X15))
      | r2_hidden(sK0,X15) ) ),
    inference(resolution,[],[f528,f65])).

fof(f528,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(sK1,X2))
      | r2_hidden(sK0,X2) ) ),
    inference(resolution,[],[f281,f75])).

fof(f281,plain,(
    ! [X2] :
      ( r1_xboole_0(sK1,X2)
      | r2_hidden(sK0,X2) ) ),
    inference(superposition,[],[f76,f233])).

fof(f2142,plain,(
    r1_tarski(sK2,sK1) ),
    inference(superposition,[],[f67,f2118])).

fof(f2118,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f2029,f495])).

fof(f495,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f487,f61])).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f487,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f72,f446])).

fof(f446,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f405,f69])).

fof(f405,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4) ),
    inference(resolution,[],[f392,f78])).

fof(f392,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(backward_demodulation,[],[f379,f382])).

fof(f382,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f377,f63])).

fof(f377,plain,(
    v1_xboole_0(k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f371,f65])).

fof(f371,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f369,f75])).

fof(f369,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f367,f233])).

fof(f367,plain,(
    r1_xboole_0(k1_tarski(sK0),sK2) ),
    inference(resolution,[],[f362,f76])).

fof(f379,plain,(
    ! [X4] : r1_tarski(k3_xboole_0(sK1,sK2),X4) ),
    inference(resolution,[],[f371,f83])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f2029,plain,(
    sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2028,f428])).

fof(f428,plain,(
    sK1 = k5_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f384,f425])).

fof(f425,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(resolution,[],[f420,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f420,plain,(
    r1_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f390,f233])).

fof(f390,plain,(
    ! [X3] : r1_xboole_0(k1_tarski(X3),k1_xboole_0) ),
    inference(backward_demodulation,[],[f376,f382])).

fof(f376,plain,(
    ! [X3] : r1_xboole_0(k1_tarski(X3),k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f371,f76])).

fof(f384,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f238,f382])).

fof(f238,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f100,f233])).

fof(f100,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f73,f56])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f2028,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2014,f68])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f2014,plain,(
    k5_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(superposition,[],[f73,f1975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:36:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (452)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (466)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (457)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (461)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.18/0.52  % (452)Refutation not found, incomplete strategy% (452)------------------------------
% 1.18/0.52  % (452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (449)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.18/0.52  % (469)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.18/0.52  % (452)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.52  
% 1.18/0.52  % (452)Memory used [KB]: 10618
% 1.18/0.52  % (452)Time elapsed: 0.102 s
% 1.18/0.52  % (452)------------------------------
% 1.18/0.52  % (452)------------------------------
% 1.18/0.53  % (446)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.18/0.53  % (450)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.18/0.53  % (459)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.54  % (442)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (441)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.54  % (451)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.54  % (470)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.55  % (456)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.55  % (453)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.55  % (471)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.55  % (467)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.55  % (454)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.33/0.55  % (448)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.55  % (443)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.55  % (460)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.33/0.56  % (462)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.56  % (465)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.33/0.56  % (451)Refutation not found, incomplete strategy% (451)------------------------------
% 1.33/0.56  % (451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (445)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.56  % (440)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.57  % (451)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.57  
% 1.33/0.57  % (451)Memory used [KB]: 10618
% 1.33/0.57  % (451)Time elapsed: 0.147 s
% 1.33/0.57  % (451)------------------------------
% 1.33/0.57  % (451)------------------------------
% 1.33/0.57  % (463)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.57  % (455)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.58  % (468)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.58  % (464)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.59  % (447)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.99/0.63  % (472)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.99/0.68  % (476)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.40/0.70  % (465)Refutation found. Thanks to Tanya!
% 2.40/0.70  % SZS status Theorem for theBenchmark
% 2.40/0.70  % SZS output start Proof for theBenchmark
% 2.40/0.70  fof(f2144,plain,(
% 2.40/0.70    $false),
% 2.40/0.70    inference(subsumption_resolution,[],[f2142,f2023])).
% 2.40/0.70  fof(f2023,plain,(
% 2.40/0.70    ~r1_tarski(sK2,sK1)),
% 2.40/0.70    inference(subsumption_resolution,[],[f1996,f282])).
% 2.40/0.70  fof(f282,plain,(
% 2.40/0.70    k1_xboole_0 != sK2),
% 2.40/0.70    inference(trivial_inequality_removal,[],[f278])).
% 2.40/0.70  fof(f278,plain,(
% 2.40/0.70    sK1 != sK1 | k1_xboole_0 != sK2),
% 2.40/0.70    inference(superposition,[],[f59,f233])).
% 2.40/0.70  fof(f233,plain,(
% 2.40/0.70    sK1 = k1_tarski(sK0)),
% 2.40/0.70    inference(subsumption_resolution,[],[f231,f163])).
% 2.40/0.70  fof(f163,plain,(
% 2.40/0.70    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 2.40/0.70    inference(resolution,[],[f160,f63])).
% 2.40/0.70  fof(f63,plain,(
% 2.40/0.70    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.40/0.70    inference(cnf_transformation,[],[f34])).
% 2.40/0.70  fof(f34,plain,(
% 2.40/0.70    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.40/0.70    inference(ennf_transformation,[],[f6])).
% 2.40/0.70  fof(f6,axiom,(
% 2.40/0.70    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.40/0.70  fof(f160,plain,(
% 2.40/0.70    v1_xboole_0(sK1) | sK1 = k1_tarski(sK0)),
% 2.40/0.70    inference(resolution,[],[f156,f65])).
% 2.40/0.70  fof(f65,plain,(
% 2.40/0.70    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 2.40/0.70    inference(cnf_transformation,[],[f45])).
% 2.40/0.70  fof(f45,plain,(
% 2.40/0.70    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.40/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 2.40/0.70  fof(f44,plain,(
% 2.40/0.70    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.40/0.70    introduced(choice_axiom,[])).
% 2.40/0.70  fof(f43,plain,(
% 2.40/0.70    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.40/0.70    inference(rectify,[],[f42])).
% 2.40/0.70  fof(f42,plain,(
% 2.40/0.70    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.40/0.70    inference(nnf_transformation,[],[f3])).
% 2.40/0.70  fof(f3,axiom,(
% 2.40/0.70    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.40/0.70  fof(f156,plain,(
% 2.40/0.70    ( ! [X0] : (~r2_hidden(X0,sK1) | sK1 = k1_tarski(sK0)) )),
% 2.40/0.70    inference(forward_demodulation,[],[f155,f105])).
% 2.40/0.70  fof(f105,plain,(
% 2.40/0.70    sK1 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 2.40/0.70    inference(resolution,[],[f101,f78])).
% 2.40/0.70  fof(f78,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.40/0.70    inference(cnf_transformation,[],[f38])).
% 2.40/0.70  fof(f38,plain,(
% 2.40/0.70    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.40/0.70    inference(ennf_transformation,[],[f13])).
% 2.40/0.70  fof(f13,axiom,(
% 2.40/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.40/0.70  fof(f101,plain,(
% 2.40/0.70    r1_tarski(sK1,k1_tarski(sK0))),
% 2.40/0.70    inference(superposition,[],[f67,f56])).
% 2.40/0.70  fof(f56,plain,(
% 2.40/0.70    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.40/0.70    inference(cnf_transformation,[],[f41])).
% 2.40/0.70  fof(f41,plain,(
% 2.40/0.70    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.40/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f40])).
% 2.40/0.70  fof(f40,plain,(
% 2.40/0.70    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.40/0.70    introduced(choice_axiom,[])).
% 2.40/0.70  fof(f33,plain,(
% 2.40/0.70    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.40/0.70    inference(ennf_transformation,[],[f30])).
% 2.40/0.70  fof(f30,negated_conjecture,(
% 2.40/0.70    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.40/0.70    inference(negated_conjecture,[],[f29])).
% 2.40/0.70  fof(f29,conjecture,(
% 2.40/0.70    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.40/0.70  fof(f67,plain,(
% 2.40/0.70    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.40/0.70    inference(cnf_transformation,[],[f15])).
% 2.40/0.70  fof(f15,axiom,(
% 2.40/0.70    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.40/0.70  fof(f155,plain,(
% 2.40/0.70    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k1_tarski(sK0))) | sK1 = k1_tarski(sK0)) )),
% 2.40/0.70    inference(forward_demodulation,[],[f154,f69])).
% 2.40/0.70  fof(f69,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.40/0.70    inference(cnf_transformation,[],[f1])).
% 2.40/0.70  fof(f1,axiom,(
% 2.40/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.40/0.70  fof(f154,plain,(
% 2.40/0.70    ( ! [X0] : (sK1 = k1_tarski(sK0) | ~r2_hidden(X0,k3_xboole_0(k1_tarski(sK0),sK1))) )),
% 2.40/0.70    inference(resolution,[],[f146,f75])).
% 2.40/0.70  fof(f75,plain,(
% 2.40/0.70    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.40/0.70    inference(cnf_transformation,[],[f47])).
% 2.40/0.70  fof(f47,plain,(
% 2.40/0.70    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.40/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f46])).
% 2.40/0.70  fof(f46,plain,(
% 2.40/0.70    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.40/0.70    introduced(choice_axiom,[])).
% 2.40/0.70  fof(f35,plain,(
% 2.40/0.70    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.40/0.70    inference(ennf_transformation,[],[f32])).
% 2.40/0.70  fof(f32,plain,(
% 2.40/0.70    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.40/0.70    inference(rectify,[],[f7])).
% 2.40/0.70  fof(f7,axiom,(
% 2.40/0.70    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.40/0.70  fof(f146,plain,(
% 2.40/0.70    r1_xboole_0(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 2.40/0.70    inference(resolution,[],[f141,f76])).
% 2.40/0.70  fof(f76,plain,(
% 2.40/0.70    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.40/0.70    inference(cnf_transformation,[],[f36])).
% 2.40/0.70  fof(f36,plain,(
% 2.40/0.70    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.40/0.70    inference(ennf_transformation,[],[f27])).
% 2.40/0.70  fof(f27,axiom,(
% 2.40/0.70    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.40/0.70  fof(f141,plain,(
% 2.40/0.70    ~r2_hidden(sK0,sK1) | sK1 = k1_tarski(sK0)),
% 2.40/0.70    inference(resolution,[],[f103,f88])).
% 2.40/0.70  fof(f88,plain,(
% 2.40/0.70    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.40/0.70    inference(cnf_transformation,[],[f55])).
% 2.40/0.70  fof(f55,plain,(
% 2.40/0.70    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.40/0.70    inference(nnf_transformation,[],[f26])).
% 2.40/0.70  fof(f26,axiom,(
% 2.40/0.70    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.40/0.70  fof(f103,plain,(
% 2.40/0.70    ~r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 2.40/0.70    inference(resolution,[],[f101,f81])).
% 2.40/0.70  fof(f81,plain,(
% 2.40/0.70    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.40/0.70    inference(cnf_transformation,[],[f49])).
% 2.40/0.70  fof(f49,plain,(
% 2.40/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.40/0.70    inference(flattening,[],[f48])).
% 2.40/0.70  fof(f48,plain,(
% 2.40/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.40/0.70    inference(nnf_transformation,[],[f8])).
% 2.40/0.70  fof(f8,axiom,(
% 2.40/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.40/0.70  fof(f231,plain,(
% 2.40/0.70    k1_xboole_0 != sK1 | sK1 = k1_tarski(sK0)),
% 2.40/0.70    inference(trivial_inequality_removal,[],[f209])).
% 2.40/0.70  fof(f209,plain,(
% 2.40/0.70    sK2 != sK2 | k1_xboole_0 != sK1 | sK1 = k1_tarski(sK0)),
% 2.40/0.70    inference(superposition,[],[f58,f169])).
% 2.40/0.70  fof(f169,plain,(
% 2.40/0.70    sK2 = k1_tarski(sK0) | sK1 = k1_tarski(sK0)),
% 2.40/0.70    inference(resolution,[],[f161,f98])).
% 2.40/0.70  fof(f98,plain,(
% 2.40/0.70    ~r1_tarski(sK1,sK2) | sK2 = k1_tarski(sK0)),
% 2.40/0.70    inference(superposition,[],[f56,f77])).
% 2.40/0.70  fof(f77,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.40/0.70    inference(cnf_transformation,[],[f37])).
% 2.40/0.70  fof(f37,plain,(
% 2.40/0.70    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.40/0.70    inference(ennf_transformation,[],[f11])).
% 2.40/0.70  fof(f11,axiom,(
% 2.40/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.40/0.70  fof(f161,plain,(
% 2.40/0.70    ( ! [X4] : (r1_tarski(sK1,X4) | sK1 = k1_tarski(sK0)) )),
% 2.40/0.70    inference(resolution,[],[f156,f83])).
% 2.40/0.70  fof(f83,plain,(
% 2.40/0.70    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 2.40/0.70    inference(cnf_transformation,[],[f53])).
% 2.40/0.70  fof(f53,plain,(
% 2.40/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f51,f52])).
% 2.40/0.70  fof(f52,plain,(
% 2.40/0.70    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.40/0.70    introduced(choice_axiom,[])).
% 2.40/0.70  fof(f51,plain,(
% 2.40/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.70    inference(rectify,[],[f50])).
% 2.40/0.70  fof(f50,plain,(
% 2.40/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.70    inference(nnf_transformation,[],[f39])).
% 2.40/0.70  fof(f39,plain,(
% 2.40/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.40/0.70    inference(ennf_transformation,[],[f4])).
% 2.40/0.70  fof(f4,axiom,(
% 2.40/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.40/0.70  fof(f58,plain,(
% 2.40/0.70    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.40/0.70    inference(cnf_transformation,[],[f41])).
% 2.40/0.70  fof(f59,plain,(
% 2.40/0.70    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.40/0.70    inference(cnf_transformation,[],[f41])).
% 2.40/0.70  fof(f1996,plain,(
% 2.40/0.70    k1_xboole_0 = sK2 | ~r1_tarski(sK2,sK1)),
% 2.40/0.70    inference(superposition,[],[f1975,f78])).
% 2.40/0.70  fof(f1975,plain,(
% 2.40/0.70    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 2.40/0.70    inference(resolution,[],[f1570,f362])).
% 2.40/0.70  fof(f362,plain,(
% 2.40/0.70    ~r2_hidden(sK0,sK2)),
% 2.40/0.70    inference(resolution,[],[f280,f266])).
% 2.40/0.70  fof(f266,plain,(
% 2.40/0.70    ~r1_tarski(sK1,sK2)),
% 2.40/0.70    inference(subsumption_resolution,[],[f237,f265])).
% 2.40/0.70  fof(f265,plain,(
% 2.40/0.70    sK1 != sK2),
% 2.40/0.70    inference(forward_demodulation,[],[f264,f233])).
% 2.40/0.70  fof(f264,plain,(
% 2.40/0.70    sK2 != k1_tarski(sK0)),
% 2.40/0.70    inference(trivial_inequality_removal,[],[f235])).
% 2.40/0.70  fof(f235,plain,(
% 2.40/0.70    sK1 != sK1 | sK2 != k1_tarski(sK0)),
% 2.40/0.70    inference(backward_demodulation,[],[f57,f233])).
% 2.40/0.70  fof(f57,plain,(
% 2.40/0.70    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.40/0.70    inference(cnf_transformation,[],[f41])).
% 2.40/0.70  fof(f237,plain,(
% 2.40/0.70    sK1 = sK2 | ~r1_tarski(sK1,sK2)),
% 2.40/0.70    inference(backward_demodulation,[],[f98,f233])).
% 2.40/0.70  fof(f280,plain,(
% 2.40/0.70    ( ! [X1] : (r1_tarski(sK1,X1) | ~r2_hidden(sK0,X1)) )),
% 2.40/0.70    inference(superposition,[],[f88,f233])).
% 2.40/0.70  fof(f1570,plain,(
% 2.40/0.70    ( ! [X0] : (r2_hidden(sK0,X0) | k1_xboole_0 = k3_xboole_0(X0,sK1)) )),
% 2.40/0.70    inference(resolution,[],[f1564,f63])).
% 2.40/0.70  fof(f1564,plain,(
% 2.40/0.70    ( ! [X5] : (v1_xboole_0(k3_xboole_0(X5,sK1)) | r2_hidden(sK0,X5)) )),
% 2.40/0.70    inference(superposition,[],[f1525,f69])).
% 2.40/0.70  fof(f1525,plain,(
% 2.40/0.70    ( ! [X15] : (v1_xboole_0(k3_xboole_0(sK1,X15)) | r2_hidden(sK0,X15)) )),
% 2.40/0.70    inference(resolution,[],[f528,f65])).
% 2.40/0.70  fof(f528,plain,(
% 2.40/0.70    ( ! [X2,X3] : (~r2_hidden(X3,k3_xboole_0(sK1,X2)) | r2_hidden(sK0,X2)) )),
% 2.40/0.70    inference(resolution,[],[f281,f75])).
% 2.40/0.70  fof(f281,plain,(
% 2.40/0.70    ( ! [X2] : (r1_xboole_0(sK1,X2) | r2_hidden(sK0,X2)) )),
% 2.40/0.70    inference(superposition,[],[f76,f233])).
% 2.40/0.70  fof(f2142,plain,(
% 2.40/0.70    r1_tarski(sK2,sK1)),
% 2.40/0.70    inference(superposition,[],[f67,f2118])).
% 2.40/0.70  fof(f2118,plain,(
% 2.40/0.70    sK1 = k2_xboole_0(sK2,sK1)),
% 2.40/0.70    inference(superposition,[],[f2029,f495])).
% 2.40/0.70  fof(f495,plain,(
% 2.40/0.70    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.40/0.70    inference(forward_demodulation,[],[f487,f61])).
% 2.40/0.70  fof(f61,plain,(
% 2.40/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.40/0.70    inference(cnf_transformation,[],[f14])).
% 2.40/0.70  fof(f14,axiom,(
% 2.40/0.70    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.40/0.70  fof(f487,plain,(
% 2.40/0.70    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 2.40/0.70    inference(superposition,[],[f72,f446])).
% 2.40/0.70  fof(f446,plain,(
% 2.40/0.70    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) )),
% 2.40/0.70    inference(superposition,[],[f405,f69])).
% 2.40/0.70  fof(f405,plain,(
% 2.40/0.70    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4)) )),
% 2.40/0.70    inference(resolution,[],[f392,f78])).
% 2.40/0.70  fof(f392,plain,(
% 2.40/0.70    ( ! [X4] : (r1_tarski(k1_xboole_0,X4)) )),
% 2.40/0.70    inference(backward_demodulation,[],[f379,f382])).
% 2.40/0.70  fof(f382,plain,(
% 2.40/0.70    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 2.40/0.70    inference(resolution,[],[f377,f63])).
% 2.40/0.70  fof(f377,plain,(
% 2.40/0.70    v1_xboole_0(k3_xboole_0(sK1,sK2))),
% 2.40/0.70    inference(resolution,[],[f371,f65])).
% 2.40/0.70  fof(f371,plain,(
% 2.40/0.70    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2))) )),
% 2.40/0.70    inference(resolution,[],[f369,f75])).
% 2.40/0.70  fof(f369,plain,(
% 2.40/0.70    r1_xboole_0(sK1,sK2)),
% 2.40/0.70    inference(forward_demodulation,[],[f367,f233])).
% 2.40/0.70  fof(f367,plain,(
% 2.40/0.70    r1_xboole_0(k1_tarski(sK0),sK2)),
% 2.40/0.70    inference(resolution,[],[f362,f76])).
% 2.40/0.70  fof(f379,plain,(
% 2.40/0.70    ( ! [X4] : (r1_tarski(k3_xboole_0(sK1,sK2),X4)) )),
% 2.40/0.70    inference(resolution,[],[f371,f83])).
% 2.40/0.70  fof(f72,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.40/0.70    inference(cnf_transformation,[],[f10])).
% 2.40/0.70  fof(f10,axiom,(
% 2.40/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.40/0.70  fof(f2029,plain,(
% 2.40/0.70    sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)),
% 2.40/0.70    inference(forward_demodulation,[],[f2028,f428])).
% 2.40/0.70  fof(f428,plain,(
% 2.40/0.70    sK1 = k5_xboole_0(sK1,sK2)),
% 2.40/0.70    inference(backward_demodulation,[],[f384,f425])).
% 2.40/0.70  fof(f425,plain,(
% 2.40/0.70    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 2.40/0.70    inference(resolution,[],[f420,f85])).
% 2.40/0.70  fof(f85,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.40/0.70    inference(cnf_transformation,[],[f54])).
% 2.40/0.70  fof(f54,plain,(
% 2.40/0.70    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.40/0.70    inference(nnf_transformation,[],[f16])).
% 2.40/0.70  fof(f16,axiom,(
% 2.40/0.70    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.40/0.70  fof(f420,plain,(
% 2.40/0.70    r1_xboole_0(sK1,k1_xboole_0)),
% 2.40/0.70    inference(superposition,[],[f390,f233])).
% 2.40/0.70  fof(f390,plain,(
% 2.40/0.70    ( ! [X3] : (r1_xboole_0(k1_tarski(X3),k1_xboole_0)) )),
% 2.40/0.70    inference(backward_demodulation,[],[f376,f382])).
% 2.40/0.70  fof(f376,plain,(
% 2.40/0.70    ( ! [X3] : (r1_xboole_0(k1_tarski(X3),k3_xboole_0(sK1,sK2))) )),
% 2.40/0.70    inference(resolution,[],[f371,f76])).
% 2.40/0.70  fof(f384,plain,(
% 2.40/0.70    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)),
% 2.40/0.70    inference(backward_demodulation,[],[f238,f382])).
% 2.40/0.70  fof(f238,plain,(
% 2.40/0.70    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.40/0.70    inference(backward_demodulation,[],[f100,f233])).
% 2.40/0.70  fof(f100,plain,(
% 2.40/0.70    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))),
% 2.40/0.70    inference(superposition,[],[f73,f56])).
% 2.40/0.70  fof(f73,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.40/0.70    inference(cnf_transformation,[],[f9])).
% 2.40/0.70  fof(f9,axiom,(
% 2.40/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.40/0.70  fof(f2028,plain,(
% 2.40/0.70    k5_xboole_0(sK1,sK2) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)),
% 2.40/0.70    inference(forward_demodulation,[],[f2014,f68])).
% 2.40/0.70  fof(f68,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.40/0.70    inference(cnf_transformation,[],[f2])).
% 2.40/0.70  fof(f2,axiom,(
% 2.40/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.40/0.70  fof(f2014,plain,(
% 2.40/0.70    k5_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)),
% 2.40/0.70    inference(superposition,[],[f73,f1975])).
% 2.40/0.70  % SZS output end Proof for theBenchmark
% 2.40/0.70  % (465)------------------------------
% 2.40/0.70  % (465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.70  % (465)Termination reason: Refutation
% 2.40/0.70  
% 2.40/0.70  % (465)Memory used [KB]: 2430
% 2.40/0.70  % (465)Time elapsed: 0.258 s
% 2.40/0.70  % (465)------------------------------
% 2.40/0.70  % (465)------------------------------
% 2.40/0.71  % (439)Success in time 0.337 s
%------------------------------------------------------------------------------
