%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:55 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  129 (6514 expanded)
%              Number of leaves         :   23 (1769 expanded)
%              Depth                    :   39
%              Number of atoms          :  282 (21729 expanded)
%              Number of equality atoms :  131 (13820 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2327,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2325,f2217])).

fof(f2217,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f2190,f299])).

fof(f299,plain,(
    k1_xboole_0 != sK2 ),
    inference(trivial_inequality_removal,[],[f295])).

fof(f295,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2 ),
    inference(superposition,[],[f60,f243])).

fof(f243,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f241,f165])).

fof(f165,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f162,f64])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f162,plain,
    ( v1_xboole_0(sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f158,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
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

fof(f158,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK1 = k1_tarski(sK0) ) ),
    inference(forward_demodulation,[],[f157,f104])).

fof(f104,plain,(
    sK1 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f101,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f101,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f68,f57])).

fof(f57,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f41])).

fof(f41,plain,
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

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f157,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK1,k1_tarski(sK0)))
      | sK1 = k1_tarski(sK0) ) ),
    inference(forward_demodulation,[],[f156,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f156,plain,(
    ! [X0] :
      ( sK1 = k1_tarski(sK0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_tarski(sK0),sK1)) ) ),
    inference(resolution,[],[f154,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f47])).

fof(f47,plain,(
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
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f154,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f149,f77])).

fof(f77,plain,(
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

fof(f149,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f118,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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

fof(f118,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f117,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f117,plain,(
    ~ r2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f90,f111])).

fof(f111,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f106,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f106,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f73,f104])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f241,plain,
    ( k1_xboole_0 != sK1
    | sK1 = k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f217])).

fof(f217,plain,
    ( sK2 != sK2
    | k1_xboole_0 != sK1
    | sK1 = k1_tarski(sK0) ),
    inference(superposition,[],[f59,f170])).

fof(f170,plain,
    ( sK2 = k1_tarski(sK0)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f163,f98])).

fof(f98,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK2 = k1_tarski(sK0) ),
    inference(superposition,[],[f57,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f163,plain,(
    ! [X4] :
      ( r1_tarski(sK1,X4)
      | sK1 = k1_tarski(sK0) ) ),
    inference(resolution,[],[f158,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f52,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
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

fof(f59,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f42])).

fof(f2190,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(sK2,sK1) ),
    inference(superposition,[],[f2169,f79])).

fof(f2169,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f1768,f379])).

fof(f379,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f297,f278])).

fof(f278,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f247,f277])).

fof(f277,plain,(
    sK1 != sK2 ),
    inference(forward_demodulation,[],[f276,f243])).

fof(f276,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f245])).

fof(f245,plain,
    ( sK1 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f58,f243])).

fof(f58,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f247,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f98,f243])).

fof(f297,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(superposition,[],[f89,f243])).

fof(f1768,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | k1_xboole_0 = k3_xboole_0(X0,sK1) ) ),
    inference(resolution,[],[f1762,f64])).

fof(f1762,plain,(
    ! [X5] :
      ( v1_xboole_0(k3_xboole_0(X5,sK1))
      | r2_hidden(sK0,X5) ) ),
    inference(superposition,[],[f1721,f70])).

fof(f1721,plain,(
    ! [X15] :
      ( v1_xboole_0(k3_xboole_0(sK1,X15))
      | r2_hidden(sK0,X15) ) ),
    inference(resolution,[],[f557,f66])).

fof(f557,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(sK1,X2))
      | r2_hidden(sK0,X2) ) ),
    inference(resolution,[],[f298,f76])).

fof(f298,plain,(
    ! [X2] :
      ( r1_xboole_0(sK1,X2)
      | r2_hidden(sK0,X2) ) ),
    inference(superposition,[],[f77,f243])).

fof(f2325,plain,(
    r1_tarski(sK2,sK1) ),
    inference(superposition,[],[f68,f2315])).

fof(f2315,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f2223,f515])).

fof(f515,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f507,f62])).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f507,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f73,f465])).

fof(f465,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f423,f70])).

fof(f423,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3) ),
    inference(resolution,[],[f411,f79])).

fof(f411,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(backward_demodulation,[],[f397,f400])).

fof(f400,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f395,f64])).

fof(f395,plain,(
    v1_xboole_0(k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f388,f66])).

fof(f388,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f386,f76])).

fof(f386,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f384,f243])).

fof(f384,plain,(
    r1_xboole_0(k1_tarski(sK0),sK2) ),
    inference(resolution,[],[f379,f77])).

fof(f397,plain,(
    ! [X4] : r1_tarski(k3_xboole_0(sK1,sK2),X4) ),
    inference(resolution,[],[f388,f84])).

fof(f2223,plain,(
    sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2222,f446])).

fof(f446,plain,(
    sK1 = k5_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f402,f443])).

fof(f443,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(resolution,[],[f438,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f438,plain,(
    r1_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f409,f243])).

fof(f409,plain,(
    ! [X3] : r1_xboole_0(k1_tarski(X3),k1_xboole_0) ),
    inference(backward_demodulation,[],[f394,f400])).

fof(f394,plain,(
    ! [X3] : r1_xboole_0(k1_tarski(X3),k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f388,f77])).

fof(f402,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f248,f400])).

fof(f248,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f100,f243])).

fof(f100,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f74,f57])).

fof(f74,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f2222,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2208,f69])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f2208,plain,(
    k5_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(superposition,[],[f74,f2169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (18392)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.47  % (18392)Refutation not found, incomplete strategy% (18392)------------------------------
% 0.20/0.47  % (18392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18407)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.48  % (18392)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (18392)Memory used [KB]: 10618
% 0.20/0.48  % (18392)Time elapsed: 0.064 s
% 0.20/0.48  % (18392)------------------------------
% 0.20/0.48  % (18392)------------------------------
% 0.20/0.50  % (18388)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.54  % (18383)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.54  % (18386)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.54  % (18401)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.54  % (18390)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.54  % (18394)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.37/0.54  % (18381)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.55  % (18387)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.55  % (18393)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.55  % (18402)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.55  % (18384)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.55  % (18410)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.55  % (18399)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.55  % (18403)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.55  % (18395)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.37/0.56  % (18404)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.56  % (18408)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.56  % (18406)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.56  % (18380)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.56  % (18405)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.56  % (18397)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.56  % (18382)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.56  % (18411)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.56  % (18396)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.57  % (18385)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.57  % (18400)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.58  % (18391)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.58  % (18391)Refutation not found, incomplete strategy% (18391)------------------------------
% 1.37/0.58  % (18391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.58  % (18391)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.58  
% 1.37/0.58  % (18391)Memory used [KB]: 10618
% 1.37/0.58  % (18391)Time elapsed: 0.163 s
% 1.37/0.58  % (18391)------------------------------
% 1.37/0.58  % (18391)------------------------------
% 1.37/0.58  % (18398)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.59  % (18441)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.00/0.67  % (18404)Refutation found. Thanks to Tanya!
% 2.00/0.67  % SZS status Theorem for theBenchmark
% 2.45/0.68  % SZS output start Proof for theBenchmark
% 2.45/0.68  fof(f2327,plain,(
% 2.45/0.68    $false),
% 2.45/0.68    inference(subsumption_resolution,[],[f2325,f2217])).
% 2.45/0.68  fof(f2217,plain,(
% 2.45/0.68    ~r1_tarski(sK2,sK1)),
% 2.45/0.68    inference(subsumption_resolution,[],[f2190,f299])).
% 2.45/0.68  fof(f299,plain,(
% 2.45/0.68    k1_xboole_0 != sK2),
% 2.45/0.68    inference(trivial_inequality_removal,[],[f295])).
% 2.45/0.68  fof(f295,plain,(
% 2.45/0.68    sK1 != sK1 | k1_xboole_0 != sK2),
% 2.45/0.68    inference(superposition,[],[f60,f243])).
% 2.45/0.68  fof(f243,plain,(
% 2.45/0.68    sK1 = k1_tarski(sK0)),
% 2.45/0.68    inference(subsumption_resolution,[],[f241,f165])).
% 2.45/0.68  fof(f165,plain,(
% 2.45/0.68    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 2.45/0.68    inference(resolution,[],[f162,f64])).
% 2.45/0.68  fof(f64,plain,(
% 2.45/0.68    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.45/0.68    inference(cnf_transformation,[],[f34])).
% 2.45/0.68  fof(f34,plain,(
% 2.45/0.68    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.45/0.68    inference(ennf_transformation,[],[f7])).
% 2.45/0.68  fof(f7,axiom,(
% 2.45/0.68    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.45/0.68  fof(f162,plain,(
% 2.45/0.68    v1_xboole_0(sK1) | sK1 = k1_tarski(sK0)),
% 2.45/0.68    inference(resolution,[],[f158,f66])).
% 2.45/0.68  fof(f66,plain,(
% 2.45/0.68    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 2.45/0.68    inference(cnf_transformation,[],[f46])).
% 2.45/0.68  fof(f46,plain,(
% 2.45/0.68    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.45/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 2.45/0.68  fof(f45,plain,(
% 2.45/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.45/0.68    introduced(choice_axiom,[])).
% 2.45/0.68  fof(f44,plain,(
% 2.45/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.45/0.68    inference(rectify,[],[f43])).
% 2.45/0.68  fof(f43,plain,(
% 2.45/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.45/0.68    inference(nnf_transformation,[],[f3])).
% 2.45/0.68  fof(f3,axiom,(
% 2.45/0.68    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.45/0.68  fof(f158,plain,(
% 2.45/0.68    ( ! [X0] : (~r2_hidden(X0,sK1) | sK1 = k1_tarski(sK0)) )),
% 2.45/0.68    inference(forward_demodulation,[],[f157,f104])).
% 2.45/0.68  fof(f104,plain,(
% 2.45/0.68    sK1 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 2.45/0.68    inference(resolution,[],[f101,f79])).
% 2.45/0.68  fof(f79,plain,(
% 2.45/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.45/0.68    inference(cnf_transformation,[],[f38])).
% 2.45/0.68  fof(f38,plain,(
% 2.45/0.68    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.45/0.68    inference(ennf_transformation,[],[f14])).
% 2.45/0.68  fof(f14,axiom,(
% 2.45/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.45/0.68  fof(f101,plain,(
% 2.45/0.68    r1_tarski(sK1,k1_tarski(sK0))),
% 2.45/0.68    inference(superposition,[],[f68,f57])).
% 2.45/0.68  fof(f57,plain,(
% 2.45/0.68    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.45/0.68    inference(cnf_transformation,[],[f42])).
% 2.45/0.68  fof(f42,plain,(
% 2.45/0.68    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.45/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f41])).
% 2.45/0.68  fof(f41,plain,(
% 2.45/0.68    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.45/0.68    introduced(choice_axiom,[])).
% 2.45/0.68  fof(f33,plain,(
% 2.45/0.68    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.45/0.68    inference(ennf_transformation,[],[f30])).
% 2.45/0.68  fof(f30,negated_conjecture,(
% 2.45/0.68    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.45/0.68    inference(negated_conjecture,[],[f29])).
% 2.45/0.68  fof(f29,conjecture,(
% 2.45/0.68    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.45/0.68  fof(f68,plain,(
% 2.45/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.45/0.68    inference(cnf_transformation,[],[f16])).
% 2.45/0.68  fof(f16,axiom,(
% 2.45/0.68    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.45/0.68  fof(f157,plain,(
% 2.45/0.68    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k1_tarski(sK0))) | sK1 = k1_tarski(sK0)) )),
% 2.45/0.68    inference(forward_demodulation,[],[f156,f70])).
% 2.45/0.68  fof(f70,plain,(
% 2.45/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.45/0.68    inference(cnf_transformation,[],[f1])).
% 2.45/0.68  fof(f1,axiom,(
% 2.45/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.45/0.68  fof(f156,plain,(
% 2.45/0.68    ( ! [X0] : (sK1 = k1_tarski(sK0) | ~r2_hidden(X0,k3_xboole_0(k1_tarski(sK0),sK1))) )),
% 2.45/0.68    inference(resolution,[],[f154,f76])).
% 2.45/0.68  fof(f76,plain,(
% 2.45/0.68    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.45/0.68    inference(cnf_transformation,[],[f48])).
% 2.45/0.68  fof(f48,plain,(
% 2.45/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.45/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f47])).
% 2.45/0.68  fof(f47,plain,(
% 2.45/0.68    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.45/0.68    introduced(choice_axiom,[])).
% 2.45/0.68  fof(f35,plain,(
% 2.45/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.45/0.68    inference(ennf_transformation,[],[f32])).
% 2.45/0.68  fof(f32,plain,(
% 2.45/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.45/0.68    inference(rectify,[],[f8])).
% 2.45/0.68  fof(f8,axiom,(
% 2.45/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.45/0.68  fof(f154,plain,(
% 2.45/0.68    r1_xboole_0(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 2.45/0.68    inference(resolution,[],[f149,f77])).
% 2.45/0.68  fof(f77,plain,(
% 2.45/0.68    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.45/0.68    inference(cnf_transformation,[],[f36])).
% 2.45/0.68  fof(f36,plain,(
% 2.45/0.68    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.45/0.68    inference(ennf_transformation,[],[f27])).
% 2.45/0.68  fof(f27,axiom,(
% 2.45/0.68    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.45/0.68  fof(f149,plain,(
% 2.45/0.68    ~r2_hidden(sK0,sK1) | sK1 = k1_tarski(sK0)),
% 2.45/0.68    inference(resolution,[],[f118,f89])).
% 2.45/0.68  fof(f89,plain,(
% 2.45/0.68    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.45/0.68    inference(cnf_transformation,[],[f56])).
% 2.45/0.68  fof(f56,plain,(
% 2.45/0.68    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.45/0.68    inference(nnf_transformation,[],[f26])).
% 2.45/0.68  fof(f26,axiom,(
% 2.45/0.68    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.45/0.68  fof(f118,plain,(
% 2.45/0.68    ~r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 2.45/0.68    inference(resolution,[],[f117,f82])).
% 2.45/0.68  fof(f82,plain,(
% 2.45/0.68    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.45/0.68    inference(cnf_transformation,[],[f50])).
% 2.45/0.68  fof(f50,plain,(
% 2.45/0.68    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.45/0.68    inference(flattening,[],[f49])).
% 2.45/0.68  fof(f49,plain,(
% 2.45/0.68    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.45/0.68    inference(nnf_transformation,[],[f5])).
% 2.45/0.68  fof(f5,axiom,(
% 2.45/0.68    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 2.45/0.68  fof(f117,plain,(
% 2.45/0.68    ~r2_xboole_0(k1_tarski(sK0),sK1)),
% 2.45/0.68    inference(trivial_inequality_removal,[],[f114])).
% 2.45/0.68  fof(f114,plain,(
% 2.45/0.68    k1_xboole_0 != k1_xboole_0 | ~r2_xboole_0(k1_tarski(sK0),sK1)),
% 2.45/0.68    inference(superposition,[],[f90,f111])).
% 2.45/0.68  fof(f111,plain,(
% 2.45/0.68    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0))),
% 2.45/0.68    inference(forward_demodulation,[],[f106,f61])).
% 2.45/0.68  fof(f61,plain,(
% 2.45/0.68    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.45/0.68    inference(cnf_transformation,[],[f19])).
% 2.45/0.68  fof(f19,axiom,(
% 2.45/0.68    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.45/0.68  fof(f106,plain,(
% 2.45/0.68    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,sK1)),
% 2.45/0.68    inference(superposition,[],[f73,f104])).
% 2.45/0.68  fof(f73,plain,(
% 2.45/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.45/0.68    inference(cnf_transformation,[],[f10])).
% 2.45/0.68  fof(f10,axiom,(
% 2.45/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.45/0.68  fof(f90,plain,(
% 2.45/0.68    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 2.45/0.68    inference(cnf_transformation,[],[f40])).
% 2.45/0.68  fof(f40,plain,(
% 2.45/0.68    ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 2.45/0.68    inference(ennf_transformation,[],[f11])).
% 2.45/0.68  fof(f11,axiom,(
% 2.45/0.68    ! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).
% 2.45/0.68  fof(f241,plain,(
% 2.45/0.68    k1_xboole_0 != sK1 | sK1 = k1_tarski(sK0)),
% 2.45/0.68    inference(trivial_inequality_removal,[],[f217])).
% 2.45/0.68  fof(f217,plain,(
% 2.45/0.68    sK2 != sK2 | k1_xboole_0 != sK1 | sK1 = k1_tarski(sK0)),
% 2.45/0.68    inference(superposition,[],[f59,f170])).
% 2.45/0.68  fof(f170,plain,(
% 2.45/0.68    sK2 = k1_tarski(sK0) | sK1 = k1_tarski(sK0)),
% 2.45/0.68    inference(resolution,[],[f163,f98])).
% 2.45/0.68  fof(f98,plain,(
% 2.45/0.68    ~r1_tarski(sK1,sK2) | sK2 = k1_tarski(sK0)),
% 2.45/0.68    inference(superposition,[],[f57,f78])).
% 2.45/0.68  fof(f78,plain,(
% 2.45/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.45/0.68    inference(cnf_transformation,[],[f37])).
% 2.45/0.68  fof(f37,plain,(
% 2.45/0.68    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.45/0.68    inference(ennf_transformation,[],[f12])).
% 2.45/0.68  fof(f12,axiom,(
% 2.45/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.45/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.45/0.68  fof(f163,plain,(
% 2.45/0.68    ( ! [X4] : (r1_tarski(sK1,X4) | sK1 = k1_tarski(sK0)) )),
% 2.45/0.68    inference(resolution,[],[f158,f84])).
% 2.45/0.68  fof(f84,plain,(
% 2.45/0.68    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 2.45/0.68    inference(cnf_transformation,[],[f54])).
% 2.45/0.68  fof(f54,plain,(
% 2.45/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.45/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f52,f53])).
% 2.45/0.68  fof(f53,plain,(
% 2.45/0.68    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.45/0.68    introduced(choice_axiom,[])).
% 2.45/0.68  fof(f52,plain,(
% 2.45/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.45/0.68    inference(rectify,[],[f51])).
% 2.45/0.68  fof(f51,plain,(
% 2.45/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.45/0.68    inference(nnf_transformation,[],[f39])).
% 2.45/0.68  fof(f39,plain,(
% 2.45/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.45/0.68    inference(ennf_transformation,[],[f4])).
% 2.45/0.69  fof(f4,axiom,(
% 2.45/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.45/0.69  fof(f59,plain,(
% 2.45/0.69    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.45/0.69    inference(cnf_transformation,[],[f42])).
% 2.45/0.69  fof(f60,plain,(
% 2.45/0.69    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.45/0.69    inference(cnf_transformation,[],[f42])).
% 2.45/0.69  fof(f2190,plain,(
% 2.45/0.69    k1_xboole_0 = sK2 | ~r1_tarski(sK2,sK1)),
% 2.45/0.69    inference(superposition,[],[f2169,f79])).
% 2.45/0.69  fof(f2169,plain,(
% 2.45/0.69    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 2.45/0.69    inference(resolution,[],[f1768,f379])).
% 2.45/0.69  fof(f379,plain,(
% 2.45/0.69    ~r2_hidden(sK0,sK2)),
% 2.45/0.69    inference(resolution,[],[f297,f278])).
% 2.45/0.69  fof(f278,plain,(
% 2.45/0.69    ~r1_tarski(sK1,sK2)),
% 2.45/0.69    inference(subsumption_resolution,[],[f247,f277])).
% 2.45/0.69  fof(f277,plain,(
% 2.45/0.69    sK1 != sK2),
% 2.45/0.69    inference(forward_demodulation,[],[f276,f243])).
% 2.45/0.69  fof(f276,plain,(
% 2.45/0.69    sK2 != k1_tarski(sK0)),
% 2.45/0.69    inference(trivial_inequality_removal,[],[f245])).
% 2.45/0.69  fof(f245,plain,(
% 2.45/0.69    sK1 != sK1 | sK2 != k1_tarski(sK0)),
% 2.45/0.69    inference(backward_demodulation,[],[f58,f243])).
% 2.45/0.69  fof(f58,plain,(
% 2.45/0.69    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.45/0.69    inference(cnf_transformation,[],[f42])).
% 2.45/0.69  fof(f247,plain,(
% 2.45/0.69    sK1 = sK2 | ~r1_tarski(sK1,sK2)),
% 2.45/0.69    inference(backward_demodulation,[],[f98,f243])).
% 2.45/0.69  fof(f297,plain,(
% 2.45/0.69    ( ! [X1] : (r1_tarski(sK1,X1) | ~r2_hidden(sK0,X1)) )),
% 2.45/0.69    inference(superposition,[],[f89,f243])).
% 2.45/0.69  fof(f1768,plain,(
% 2.45/0.69    ( ! [X0] : (r2_hidden(sK0,X0) | k1_xboole_0 = k3_xboole_0(X0,sK1)) )),
% 2.45/0.69    inference(resolution,[],[f1762,f64])).
% 2.45/0.69  fof(f1762,plain,(
% 2.45/0.69    ( ! [X5] : (v1_xboole_0(k3_xboole_0(X5,sK1)) | r2_hidden(sK0,X5)) )),
% 2.45/0.69    inference(superposition,[],[f1721,f70])).
% 2.45/0.69  fof(f1721,plain,(
% 2.45/0.69    ( ! [X15] : (v1_xboole_0(k3_xboole_0(sK1,X15)) | r2_hidden(sK0,X15)) )),
% 2.45/0.69    inference(resolution,[],[f557,f66])).
% 2.45/0.69  fof(f557,plain,(
% 2.45/0.69    ( ! [X2,X3] : (~r2_hidden(X3,k3_xboole_0(sK1,X2)) | r2_hidden(sK0,X2)) )),
% 2.45/0.69    inference(resolution,[],[f298,f76])).
% 2.45/0.69  fof(f298,plain,(
% 2.45/0.69    ( ! [X2] : (r1_xboole_0(sK1,X2) | r2_hidden(sK0,X2)) )),
% 2.45/0.69    inference(superposition,[],[f77,f243])).
% 2.45/0.69  fof(f2325,plain,(
% 2.45/0.69    r1_tarski(sK2,sK1)),
% 2.45/0.69    inference(superposition,[],[f68,f2315])).
% 2.45/0.69  fof(f2315,plain,(
% 2.45/0.69    sK1 = k2_xboole_0(sK2,sK1)),
% 2.45/0.69    inference(superposition,[],[f2223,f515])).
% 2.45/0.69  fof(f515,plain,(
% 2.45/0.69    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.45/0.69    inference(forward_demodulation,[],[f507,f62])).
% 2.45/0.69  fof(f62,plain,(
% 2.45/0.69    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.45/0.69    inference(cnf_transformation,[],[f15])).
% 2.45/0.69  fof(f15,axiom,(
% 2.45/0.69    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.45/0.69  fof(f507,plain,(
% 2.45/0.69    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 2.45/0.69    inference(superposition,[],[f73,f465])).
% 2.45/0.69  fof(f465,plain,(
% 2.45/0.69    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) )),
% 2.45/0.69    inference(superposition,[],[f423,f70])).
% 2.45/0.69  fof(f423,plain,(
% 2.45/0.69    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) )),
% 2.45/0.69    inference(resolution,[],[f411,f79])).
% 2.45/0.69  fof(f411,plain,(
% 2.45/0.69    ( ! [X4] : (r1_tarski(k1_xboole_0,X4)) )),
% 2.45/0.69    inference(backward_demodulation,[],[f397,f400])).
% 2.45/0.69  fof(f400,plain,(
% 2.45/0.69    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 2.45/0.69    inference(resolution,[],[f395,f64])).
% 2.45/0.69  fof(f395,plain,(
% 2.45/0.69    v1_xboole_0(k3_xboole_0(sK1,sK2))),
% 2.45/0.69    inference(resolution,[],[f388,f66])).
% 2.45/0.69  fof(f388,plain,(
% 2.45/0.69    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2))) )),
% 2.45/0.69    inference(resolution,[],[f386,f76])).
% 2.45/0.69  fof(f386,plain,(
% 2.45/0.69    r1_xboole_0(sK1,sK2)),
% 2.45/0.69    inference(forward_demodulation,[],[f384,f243])).
% 2.45/0.69  fof(f384,plain,(
% 2.45/0.69    r1_xboole_0(k1_tarski(sK0),sK2)),
% 2.45/0.69    inference(resolution,[],[f379,f77])).
% 2.45/0.69  fof(f397,plain,(
% 2.45/0.69    ( ! [X4] : (r1_tarski(k3_xboole_0(sK1,sK2),X4)) )),
% 2.45/0.69    inference(resolution,[],[f388,f84])).
% 2.45/0.69  fof(f2223,plain,(
% 2.45/0.69    sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)),
% 2.45/0.69    inference(forward_demodulation,[],[f2222,f446])).
% 2.45/0.69  fof(f446,plain,(
% 2.45/0.69    sK1 = k5_xboole_0(sK1,sK2)),
% 2.45/0.69    inference(backward_demodulation,[],[f402,f443])).
% 2.45/0.69  fof(f443,plain,(
% 2.45/0.69    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 2.45/0.69    inference(resolution,[],[f438,f86])).
% 2.45/0.69  fof(f86,plain,(
% 2.45/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f55])).
% 2.45/0.69  fof(f55,plain,(
% 2.45/0.69    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.45/0.69    inference(nnf_transformation,[],[f17])).
% 2.45/0.69  fof(f17,axiom,(
% 2.45/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.45/0.69  fof(f438,plain,(
% 2.45/0.69    r1_xboole_0(sK1,k1_xboole_0)),
% 2.45/0.69    inference(superposition,[],[f409,f243])).
% 2.45/0.69  fof(f409,plain,(
% 2.45/0.69    ( ! [X3] : (r1_xboole_0(k1_tarski(X3),k1_xboole_0)) )),
% 2.45/0.69    inference(backward_demodulation,[],[f394,f400])).
% 2.45/0.69  fof(f394,plain,(
% 2.45/0.69    ( ! [X3] : (r1_xboole_0(k1_tarski(X3),k3_xboole_0(sK1,sK2))) )),
% 2.45/0.69    inference(resolution,[],[f388,f77])).
% 2.45/0.69  fof(f402,plain,(
% 2.45/0.69    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)),
% 2.45/0.69    inference(backward_demodulation,[],[f248,f400])).
% 2.45/0.69  fof(f248,plain,(
% 2.45/0.69    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.45/0.69    inference(backward_demodulation,[],[f100,f243])).
% 2.45/0.69  fof(f100,plain,(
% 2.45/0.69    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))),
% 2.45/0.69    inference(superposition,[],[f74,f57])).
% 2.45/0.69  fof(f74,plain,(
% 2.45/0.69    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.45/0.69    inference(cnf_transformation,[],[f9])).
% 2.45/0.69  fof(f9,axiom,(
% 2.45/0.69    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.45/0.69  fof(f2222,plain,(
% 2.45/0.69    k5_xboole_0(sK1,sK2) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)),
% 2.45/0.69    inference(forward_demodulation,[],[f2208,f69])).
% 2.45/0.69  fof(f69,plain,(
% 2.45/0.69    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f2])).
% 2.45/0.69  fof(f2,axiom,(
% 2.45/0.69    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.45/0.69  fof(f2208,plain,(
% 2.45/0.69    k5_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)),
% 2.45/0.69    inference(superposition,[],[f74,f2169])).
% 2.45/0.69  % SZS output end Proof for theBenchmark
% 2.45/0.69  % (18404)------------------------------
% 2.45/0.69  % (18404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.45/0.69  % (18404)Termination reason: Refutation
% 2.45/0.69  
% 2.45/0.69  % (18404)Memory used [KB]: 2558
% 2.45/0.69  % (18404)Time elapsed: 0.258 s
% 2.45/0.69  % (18404)------------------------------
% 2.45/0.69  % (18404)------------------------------
% 2.45/0.69  % (18378)Success in time 0.331 s
%------------------------------------------------------------------------------
