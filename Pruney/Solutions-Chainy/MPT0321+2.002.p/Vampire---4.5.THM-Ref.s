%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:28 EST 2020

% Result     : Theorem 14.58s
% Output     : Refutation 14.58s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 738 expanded)
%              Number of leaves         :   15 ( 209 expanded)
%              Depth                    :   31
%              Number of atoms          :  189 (1962 expanded)
%              Number of equality atoms :  104 (1373 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40785,plain,(
    $false ),
    inference(global_subsumption,[],[f33768,f40779])).

fof(f40779,plain,(
    r1_tarski(sK1,sK3) ),
    inference(resolution,[],[f33295,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f33295,plain,(
    ! [X5] :
      ( ~ r1_tarski(k2_zfmisc_1(X5,sK2),k2_zfmisc_1(sK1,sK2))
      | r1_tarski(X5,sK3) ) ),
    inference(global_subsumption,[],[f47,f32969])).

fof(f32969,plain,(
    ! [X5] :
      ( ~ r1_tarski(k2_zfmisc_1(X5,sK2),k2_zfmisc_1(sK1,sK2))
      | r1_tarski(X5,sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f76,f32872])).

fof(f32872,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK2) ),
    inference(resolution,[],[f32340,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f12,f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f32340,plain,(
    sP0(sK2,sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f31391,f32254])).

fof(f32254,plain,(
    sK3 = k3_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f32252,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f32252,plain,(
    sK3 = k3_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f32250,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f32250,plain,(
    r1_tarski(sK3,sK1) ),
    inference(global_subsumption,[],[f47,f32246])).

fof(f32246,plain,
    ( r1_tarski(sK3,sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f31671,f76])).

fof(f31671,plain,(
    r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f2470,f31386])).

fof(f31386,plain,(
    sK2 = k3_xboole_0(sK2,sK4) ),
    inference(resolution,[],[f31383,f58])).

fof(f31383,plain,(
    r1_tarski(sK2,sK4) ),
    inference(global_subsumption,[],[f46,f31379])).

fof(f31379,plain,
    ( r1_tarski(sK2,sK4)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f31336,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f31336,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK4)) ),
    inference(superposition,[],[f2390,f31335])).

fof(f31335,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,k3_xboole_0(sK2,sK4)) ),
    inference(resolution,[],[f31332,f75])).

fof(f31332,plain,(
    sP0(k3_xboole_0(sK2,sK4),sK1,k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f31184,f130])).

fof(f130,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k2_xboole_0(X4,X3)) = X3 ),
    inference(resolution,[],[f58,f87])).

fof(f87,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f51,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f31184,plain,(
    ! [X0] : sP0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK1,k2_xboole_0(sK3,X0)),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f6989,f1729])).

fof(f1729,plain,(
    ! [X1] : k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k2_xboole_0(sK3,X1),sK4)) ),
    inference(resolution,[],[f1715,f58])).

fof(f1715,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k2_xboole_0(sK3,X0),sK4)) ),
    inference(superposition,[],[f1501,f45])).

fof(f45,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( sK2 != sK4
      | sK1 != sK3 )
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK2 != sK4
        | sK1 != sK3 )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f1501,plain,(
    ! [X4,X2,X3] : r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(k2_xboole_0(X2,X4),X3)) ),
    inference(superposition,[],[f51,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f6989,plain,(
    ! [X59,X57,X58,X56] : sP0(k3_xboole_0(X58,X59),k3_xboole_0(X56,X57),k3_xboole_0(k2_zfmisc_1(X56,X58),k2_zfmisc_1(X57,X59))) ),
    inference(superposition,[],[f82,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f82,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2390,plain,(
    ! [X30,X31,X29] : r1_tarski(k2_zfmisc_1(X31,k3_xboole_0(X29,X30)),k2_zfmisc_1(X31,X30)) ),
    inference(superposition,[],[f2322,f103])).

fof(f103,plain,(
    ! [X8,X7] : k2_xboole_0(k3_xboole_0(X7,X8),X8) = X8 ),
    inference(resolution,[],[f57,f92])).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f52,f54])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2322,plain,(
    ! [X6,X4,X5] : r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X4,k2_xboole_0(X5,X6))) ),
    inference(superposition,[],[f51,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f2470,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(X0,sK4)),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f2463,f54])).

fof(f2463,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,X0)),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f2389,f45])).

fof(f2389,plain,(
    ! [X28,X26,X27] : r1_tarski(k2_zfmisc_1(X28,k3_xboole_0(X26,X27)),k2_zfmisc_1(X28,X26)) ),
    inference(superposition,[],[f2322,f102])).

fof(f102,plain,(
    ! [X6,X5] : k2_xboole_0(k3_xboole_0(X5,X6),X5) = X5 ),
    inference(resolution,[],[f57,f52])).

fof(f31391,plain,(
    sP0(sK2,k3_xboole_0(sK1,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f31316,f31386])).

fof(f31316,plain,(
    sP0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK1,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f31184,f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f33768,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(global_subsumption,[],[f32251,f33765])).

fof(f33765,plain,(
    sK1 != sK3 ),
    inference(global_subsumption,[],[f46,f33764])).

fof(f33764,plain,
    ( k1_xboole_0 = sK1
    | sK1 != sK3 ),
    inference(inner_rewriting,[],[f33760])).

fof(f33760,plain,
    ( k1_xboole_0 = sK3
    | sK1 != sK3 ),
    inference(resolution,[],[f33743,f31384])).

fof(f31384,plain,
    ( ~ r1_tarski(sK4,sK2)
    | sK1 != sK3 ),
    inference(subsumption_resolution,[],[f201,f31383])).

fof(f201,plain,
    ( ~ r1_tarski(sK4,sK2)
    | ~ r1_tarski(sK2,sK4)
    | sK1 != sK3 ),
    inference(extensionality_resolution,[],[f61,f48])).

fof(f48,plain,
    ( sK2 != sK4
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f33743,plain,
    ( r1_tarski(sK4,sK2)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f33710,f50])).

fof(f33710,plain,(
    ! [X0] :
      ( r1_tarski(sK4,k2_xboole_0(sK2,X0))
      | k1_xboole_0 = sK3 ) ),
    inference(resolution,[],[f33008,f6245])).

fof(f6245,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X0))
      | r1_tarski(sK4,X0)
      | k1_xboole_0 = sK3 ) ),
    inference(superposition,[],[f77,f45])).

fof(f33008,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k2_xboole_0(sK2,X0))) ),
    inference(backward_demodulation,[],[f2377,f33007])).

fof(f33007,plain,(
    ! [X0] : k2_zfmisc_1(sK3,k2_xboole_0(sK4,X0)) = k2_zfmisc_1(sK3,k2_xboole_0(sK2,X0)) ),
    inference(backward_demodulation,[],[f2302,f32966])).

fof(f32966,plain,(
    ! [X2] : k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X2)) = k2_zfmisc_1(sK3,k2_xboole_0(sK2,X2)) ),
    inference(superposition,[],[f65,f32872])).

fof(f2302,plain,(
    ! [X0] : k2_zfmisc_1(sK3,k2_xboole_0(sK4,X0)) = k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X0)) ),
    inference(superposition,[],[f65,f45])).

fof(f2377,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k2_xboole_0(sK4,X0))) ),
    inference(superposition,[],[f2322,f45])).

fof(f32251,plain,
    ( ~ r1_tarski(sK1,sK3)
    | sK1 = sK3 ),
    inference(resolution,[],[f32250,f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (10026)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.48  % (10041)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  % (10027)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (10029)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (10025)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (10037)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (10024)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (10031)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (10022)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (10035)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (10040)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (10033)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (10044)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (10046)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.53  % (10036)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (10021)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.53  % (10043)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (10023)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.53  % (10028)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.54  % (10038)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.54  % (10042)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.54  % (10045)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.54  % (10030)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.54  % (10047)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.54  % (10034)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.54  % (10039)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 4.03/0.92  % (10021)Time limit reached!
% 4.03/0.92  % (10021)------------------------------
% 4.03/0.92  % (10021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.92  % (10035)Time limit reached!
% 4.03/0.92  % (10035)------------------------------
% 4.03/0.92  % (10035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.94  % (10021)Termination reason: Time limit
% 4.03/0.94  % (10021)Termination phase: Saturation
% 4.03/0.94  
% 4.03/0.94  % (10021)Memory used [KB]: 15095
% 4.03/0.94  % (10021)Time elapsed: 0.500 s
% 4.03/0.94  % (10021)------------------------------
% 4.03/0.94  % (10021)------------------------------
% 4.03/0.94  % (10036)Time limit reached!
% 4.03/0.94  % (10036)------------------------------
% 4.03/0.94  % (10036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.94  % (10036)Termination reason: Time limit
% 4.03/0.94  % (10036)Termination phase: Saturation
% 4.03/0.94  
% 4.03/0.94  % (10036)Memory used [KB]: 8571
% 4.03/0.94  % (10036)Time elapsed: 0.500 s
% 4.03/0.94  % (10036)------------------------------
% 4.03/0.94  % (10036)------------------------------
% 4.03/0.94  % (10035)Termination reason: Time limit
% 4.03/0.94  
% 4.03/0.94  % (10035)Memory used [KB]: 10874
% 4.03/0.94  % (10035)Time elapsed: 0.523 s
% 4.03/0.94  % (10035)------------------------------
% 4.03/0.94  % (10035)------------------------------
% 5.27/1.03  % (10027)Time limit reached!
% 5.27/1.03  % (10027)------------------------------
% 5.27/1.03  % (10027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.27/1.04  % (10027)Termination reason: Time limit
% 5.27/1.04  % (10027)Termination phase: Saturation
% 5.27/1.04  
% 5.27/1.04  % (10027)Memory used [KB]: 17910
% 5.27/1.04  % (10027)Time elapsed: 0.600 s
% 5.27/1.04  % (10027)------------------------------
% 5.27/1.04  % (10027)------------------------------
% 7.27/1.34  % (10029)Time limit reached!
% 7.27/1.34  % (10029)------------------------------
% 7.27/1.34  % (10029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.27/1.34  % (10029)Termination reason: Time limit
% 7.27/1.34  % (10029)Termination phase: Saturation
% 7.27/1.34  
% 7.27/1.34  % (10029)Memory used [KB]: 6780
% 7.27/1.34  % (10029)Time elapsed: 0.900 s
% 7.27/1.34  % (10029)------------------------------
% 7.27/1.34  % (10029)------------------------------
% 8.32/1.42  % (10022)Time limit reached!
% 8.32/1.42  % (10022)------------------------------
% 8.32/1.42  % (10022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.32/1.42  % (10022)Termination reason: Time limit
% 8.32/1.42  % (10022)Termination phase: Saturation
% 8.32/1.42  
% 8.32/1.42  % (10022)Memory used [KB]: 20596
% 8.32/1.42  % (10022)Time elapsed: 1.0000 s
% 8.32/1.42  % (10022)------------------------------
% 8.32/1.42  % (10022)------------------------------
% 9.14/1.52  % (10025)Time limit reached!
% 9.14/1.52  % (10025)------------------------------
% 9.14/1.52  % (10025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.14/1.52  % (10025)Termination reason: Time limit
% 9.14/1.52  % (10025)Termination phase: Saturation
% 9.14/1.52  
% 9.14/1.52  % (10025)Memory used [KB]: 16502
% 9.14/1.52  % (10025)Time elapsed: 1.100 s
% 9.14/1.52  % (10025)------------------------------
% 9.14/1.52  % (10025)------------------------------
% 14.58/2.22  % (10034)Refutation found. Thanks to Tanya!
% 14.58/2.22  % SZS status Theorem for theBenchmark
% 14.58/2.23  % SZS output start Proof for theBenchmark
% 14.58/2.24  fof(f40785,plain,(
% 14.58/2.24    $false),
% 14.58/2.24    inference(global_subsumption,[],[f33768,f40779])).
% 14.58/2.24  fof(f40779,plain,(
% 14.58/2.24    r1_tarski(sK1,sK3)),
% 14.58/2.24    inference(resolution,[],[f33295,f79])).
% 14.58/2.24  fof(f79,plain,(
% 14.58/2.24    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 14.58/2.24    inference(equality_resolution,[],[f60])).
% 14.58/2.24  fof(f60,plain,(
% 14.58/2.24    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 14.58/2.24    inference(cnf_transformation,[],[f36])).
% 14.58/2.24  fof(f36,plain,(
% 14.58/2.24    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 14.58/2.24    inference(flattening,[],[f35])).
% 14.58/2.24  fof(f35,plain,(
% 14.58/2.24    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 14.58/2.24    inference(nnf_transformation,[],[f7])).
% 14.58/2.24  fof(f7,axiom,(
% 14.58/2.24    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 14.58/2.24  fof(f33295,plain,(
% 14.58/2.24    ( ! [X5] : (~r1_tarski(k2_zfmisc_1(X5,sK2),k2_zfmisc_1(sK1,sK2)) | r1_tarski(X5,sK3)) )),
% 14.58/2.24    inference(global_subsumption,[],[f47,f32969])).
% 14.58/2.24  fof(f32969,plain,(
% 14.58/2.24    ( ! [X5] : (~r1_tarski(k2_zfmisc_1(X5,sK2),k2_zfmisc_1(sK1,sK2)) | r1_tarski(X5,sK3) | k1_xboole_0 = sK2) )),
% 14.58/2.24    inference(superposition,[],[f76,f32872])).
% 14.58/2.24  fof(f32872,plain,(
% 14.58/2.24    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK2)),
% 14.58/2.24    inference(resolution,[],[f32340,f75])).
% 14.58/2.24  fof(f75,plain,(
% 14.58/2.24    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 14.58/2.24    inference(cnf_transformation,[],[f44])).
% 14.58/2.24  fof(f44,plain,(
% 14.58/2.24    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 14.58/2.24    inference(nnf_transformation,[],[f28])).
% 14.58/2.24  fof(f28,plain,(
% 14.58/2.24    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 14.58/2.24    inference(definition_folding,[],[f12,f27])).
% 14.58/2.24  fof(f27,plain,(
% 14.58/2.24    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 14.58/2.24    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 14.58/2.24  fof(f12,axiom,(
% 14.58/2.24    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 14.58/2.24  fof(f32340,plain,(
% 14.58/2.24    sP0(sK2,sK3,k2_zfmisc_1(sK1,sK2))),
% 14.58/2.24    inference(backward_demodulation,[],[f31391,f32254])).
% 14.58/2.24  fof(f32254,plain,(
% 14.58/2.24    sK3 = k3_xboole_0(sK1,sK3)),
% 14.58/2.24    inference(superposition,[],[f32252,f54])).
% 14.58/2.24  fof(f54,plain,(
% 14.58/2.24    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 14.58/2.24    inference(cnf_transformation,[],[f2])).
% 14.58/2.24  fof(f2,axiom,(
% 14.58/2.24    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 14.58/2.24  fof(f32252,plain,(
% 14.58/2.24    sK3 = k3_xboole_0(sK3,sK1)),
% 14.58/2.24    inference(resolution,[],[f32250,f58])).
% 14.58/2.24  fof(f58,plain,(
% 14.58/2.24    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 14.58/2.24    inference(cnf_transformation,[],[f25])).
% 14.58/2.24  fof(f25,plain,(
% 14.58/2.24    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 14.58/2.24    inference(ennf_transformation,[],[f10])).
% 14.58/2.24  fof(f10,axiom,(
% 14.58/2.24    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 14.58/2.24  fof(f32250,plain,(
% 14.58/2.24    r1_tarski(sK3,sK1)),
% 14.58/2.24    inference(global_subsumption,[],[f47,f32246])).
% 14.58/2.24  fof(f32246,plain,(
% 14.58/2.24    r1_tarski(sK3,sK1) | k1_xboole_0 = sK2),
% 14.58/2.24    inference(resolution,[],[f31671,f76])).
% 14.58/2.24  fof(f31671,plain,(
% 14.58/2.24    r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK1,sK2))),
% 14.58/2.24    inference(superposition,[],[f2470,f31386])).
% 14.58/2.24  fof(f31386,plain,(
% 14.58/2.24    sK2 = k3_xboole_0(sK2,sK4)),
% 14.58/2.24    inference(resolution,[],[f31383,f58])).
% 14.58/2.24  fof(f31383,plain,(
% 14.58/2.24    r1_tarski(sK2,sK4)),
% 14.58/2.24    inference(global_subsumption,[],[f46,f31379])).
% 14.58/2.24  fof(f31379,plain,(
% 14.58/2.24    r1_tarski(sK2,sK4) | k1_xboole_0 = sK1),
% 14.58/2.24    inference(resolution,[],[f31336,f77])).
% 14.58/2.24  fof(f77,plain,(
% 14.58/2.24    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 14.58/2.24    inference(cnf_transformation,[],[f26])).
% 14.58/2.24  fof(f26,plain,(
% 14.58/2.24    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 14.58/2.24    inference(ennf_transformation,[],[f13])).
% 14.58/2.24  fof(f13,axiom,(
% 14.58/2.24    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 14.58/2.24  fof(f31336,plain,(
% 14.58/2.24    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK4))),
% 14.58/2.24    inference(superposition,[],[f2390,f31335])).
% 14.58/2.24  fof(f31335,plain,(
% 14.58/2.24    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,k3_xboole_0(sK2,sK4))),
% 14.58/2.24    inference(resolution,[],[f31332,f75])).
% 14.58/2.24  fof(f31332,plain,(
% 14.58/2.24    sP0(k3_xboole_0(sK2,sK4),sK1,k2_zfmisc_1(sK1,sK2))),
% 14.58/2.24    inference(superposition,[],[f31184,f130])).
% 14.58/2.24  fof(f130,plain,(
% 14.58/2.24    ( ! [X4,X3] : (k3_xboole_0(X3,k2_xboole_0(X4,X3)) = X3) )),
% 14.58/2.24    inference(resolution,[],[f58,f87])).
% 14.58/2.24  fof(f87,plain,(
% 14.58/2.24    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 14.58/2.24    inference(superposition,[],[f51,f53])).
% 14.58/2.24  fof(f53,plain,(
% 14.58/2.24    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 14.58/2.24    inference(cnf_transformation,[],[f1])).
% 14.58/2.24  fof(f1,axiom,(
% 14.58/2.24    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 14.58/2.24  fof(f51,plain,(
% 14.58/2.24    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 14.58/2.24    inference(cnf_transformation,[],[f11])).
% 14.58/2.24  fof(f11,axiom,(
% 14.58/2.24    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 14.58/2.24  fof(f31184,plain,(
% 14.58/2.24    ( ! [X0] : (sP0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK1,k2_xboole_0(sK3,X0)),k2_zfmisc_1(sK1,sK2))) )),
% 14.58/2.24    inference(superposition,[],[f6989,f1729])).
% 14.58/2.24  fof(f1729,plain,(
% 14.58/2.24    ( ! [X1] : (k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k2_xboole_0(sK3,X1),sK4))) )),
% 14.58/2.24    inference(resolution,[],[f1715,f58])).
% 14.58/2.24  fof(f1715,plain,(
% 14.58/2.24    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k2_xboole_0(sK3,X0),sK4))) )),
% 14.58/2.24    inference(superposition,[],[f1501,f45])).
% 14.58/2.24  fof(f45,plain,(
% 14.58/2.24    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4)),
% 14.58/2.24    inference(cnf_transformation,[],[f30])).
% 14.58/2.24  fof(f30,plain,(
% 14.58/2.24    (sK2 != sK4 | sK1 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4)),
% 14.58/2.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f29])).
% 14.58/2.24  fof(f29,plain,(
% 14.58/2.24    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK2 != sK4 | sK1 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4))),
% 14.58/2.24    introduced(choice_axiom,[])).
% 14.58/2.24  fof(f21,plain,(
% 14.58/2.24    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 14.58/2.24    inference(flattening,[],[f20])).
% 14.58/2.24  fof(f20,plain,(
% 14.58/2.24    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 14.58/2.24    inference(ennf_transformation,[],[f17])).
% 14.58/2.24  fof(f17,negated_conjecture,(
% 14.58/2.24    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 14.58/2.24    inference(negated_conjecture,[],[f16])).
% 14.58/2.24  fof(f16,conjecture,(
% 14.58/2.24    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 14.58/2.24  fof(f1501,plain,(
% 14.58/2.24    ( ! [X4,X2,X3] : (r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(k2_xboole_0(X2,X4),X3))) )),
% 14.58/2.24    inference(superposition,[],[f51,f64])).
% 14.58/2.24  fof(f64,plain,(
% 14.58/2.24    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 14.58/2.24    inference(cnf_transformation,[],[f14])).
% 14.58/2.24  fof(f14,axiom,(
% 14.58/2.24    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 14.58/2.24  fof(f6989,plain,(
% 14.58/2.24    ( ! [X59,X57,X58,X56] : (sP0(k3_xboole_0(X58,X59),k3_xboole_0(X56,X57),k3_xboole_0(k2_zfmisc_1(X56,X58),k2_zfmisc_1(X57,X59)))) )),
% 14.58/2.24    inference(superposition,[],[f82,f78])).
% 14.58/2.24  fof(f78,plain,(
% 14.58/2.24    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 14.58/2.24    inference(cnf_transformation,[],[f15])).
% 14.58/2.24  fof(f15,axiom,(
% 14.58/2.24    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 14.58/2.24  fof(f82,plain,(
% 14.58/2.24    ( ! [X0,X1] : (sP0(X1,X0,k2_zfmisc_1(X0,X1))) )),
% 14.58/2.24    inference(equality_resolution,[],[f74])).
% 14.58/2.24  fof(f74,plain,(
% 14.58/2.24    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 14.58/2.24    inference(cnf_transformation,[],[f44])).
% 14.58/2.24  fof(f2390,plain,(
% 14.58/2.24    ( ! [X30,X31,X29] : (r1_tarski(k2_zfmisc_1(X31,k3_xboole_0(X29,X30)),k2_zfmisc_1(X31,X30))) )),
% 14.58/2.24    inference(superposition,[],[f2322,f103])).
% 14.58/2.24  fof(f103,plain,(
% 14.58/2.24    ( ! [X8,X7] : (k2_xboole_0(k3_xboole_0(X7,X8),X8) = X8) )),
% 14.58/2.24    inference(resolution,[],[f57,f92])).
% 14.58/2.24  fof(f92,plain,(
% 14.58/2.24    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 14.58/2.24    inference(superposition,[],[f52,f54])).
% 14.58/2.24  fof(f52,plain,(
% 14.58/2.24    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 14.58/2.24    inference(cnf_transformation,[],[f9])).
% 14.58/2.24  fof(f9,axiom,(
% 14.58/2.24    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 14.58/2.24  fof(f57,plain,(
% 14.58/2.24    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 14.58/2.24    inference(cnf_transformation,[],[f24])).
% 14.58/2.24  fof(f24,plain,(
% 14.58/2.24    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 14.58/2.24    inference(ennf_transformation,[],[f8])).
% 14.58/2.24  fof(f8,axiom,(
% 14.58/2.24    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 14.58/2.24  fof(f2322,plain,(
% 14.58/2.24    ( ! [X6,X4,X5] : (r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X4,k2_xboole_0(X5,X6)))) )),
% 14.58/2.24    inference(superposition,[],[f51,f65])).
% 14.58/2.24  fof(f65,plain,(
% 14.58/2.24    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 14.58/2.24    inference(cnf_transformation,[],[f14])).
% 14.58/2.24  fof(f46,plain,(
% 14.58/2.24    k1_xboole_0 != sK1),
% 14.58/2.24    inference(cnf_transformation,[],[f30])).
% 14.58/2.24  fof(f2470,plain,(
% 14.58/2.24    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(X0,sK4)),k2_zfmisc_1(sK1,sK2))) )),
% 14.58/2.24    inference(superposition,[],[f2463,f54])).
% 14.58/2.24  fof(f2463,plain,(
% 14.58/2.24    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,X0)),k2_zfmisc_1(sK1,sK2))) )),
% 14.58/2.24    inference(superposition,[],[f2389,f45])).
% 14.58/2.24  fof(f2389,plain,(
% 14.58/2.24    ( ! [X28,X26,X27] : (r1_tarski(k2_zfmisc_1(X28,k3_xboole_0(X26,X27)),k2_zfmisc_1(X28,X26))) )),
% 14.58/2.24    inference(superposition,[],[f2322,f102])).
% 14.58/2.24  fof(f102,plain,(
% 14.58/2.24    ( ! [X6,X5] : (k2_xboole_0(k3_xboole_0(X5,X6),X5) = X5) )),
% 14.58/2.24    inference(resolution,[],[f57,f52])).
% 14.58/2.24  fof(f31391,plain,(
% 14.58/2.24    sP0(sK2,k3_xboole_0(sK1,sK3),k2_zfmisc_1(sK1,sK2))),
% 14.58/2.24    inference(backward_demodulation,[],[f31316,f31386])).
% 14.58/2.24  fof(f31316,plain,(
% 14.58/2.24    sP0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK1,sK3),k2_zfmisc_1(sK1,sK2))),
% 14.58/2.24    inference(superposition,[],[f31184,f50])).
% 14.58/2.24  fof(f50,plain,(
% 14.58/2.24    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 14.58/2.24    inference(cnf_transformation,[],[f18])).
% 14.58/2.24  fof(f18,plain,(
% 14.58/2.24    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 14.58/2.24    inference(rectify,[],[f4])).
% 14.58/2.24  fof(f4,axiom,(
% 14.58/2.24    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 14.58/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 14.58/2.24  fof(f76,plain,(
% 14.58/2.24    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 14.58/2.24    inference(cnf_transformation,[],[f26])).
% 14.58/2.24  fof(f47,plain,(
% 14.58/2.24    k1_xboole_0 != sK2),
% 14.58/2.24    inference(cnf_transformation,[],[f30])).
% 14.58/2.25  fof(f33768,plain,(
% 14.58/2.25    ~r1_tarski(sK1,sK3)),
% 14.58/2.25    inference(global_subsumption,[],[f32251,f33765])).
% 14.58/2.25  fof(f33765,plain,(
% 14.58/2.25    sK1 != sK3),
% 14.58/2.25    inference(global_subsumption,[],[f46,f33764])).
% 14.58/2.25  fof(f33764,plain,(
% 14.58/2.25    k1_xboole_0 = sK1 | sK1 != sK3),
% 14.58/2.25    inference(inner_rewriting,[],[f33760])).
% 14.58/2.25  fof(f33760,plain,(
% 14.58/2.25    k1_xboole_0 = sK3 | sK1 != sK3),
% 14.58/2.25    inference(resolution,[],[f33743,f31384])).
% 14.58/2.25  fof(f31384,plain,(
% 14.58/2.25    ~r1_tarski(sK4,sK2) | sK1 != sK3),
% 14.58/2.25    inference(subsumption_resolution,[],[f201,f31383])).
% 14.58/2.25  fof(f201,plain,(
% 14.58/2.25    ~r1_tarski(sK4,sK2) | ~r1_tarski(sK2,sK4) | sK1 != sK3),
% 14.58/2.25    inference(extensionality_resolution,[],[f61,f48])).
% 14.58/2.25  fof(f48,plain,(
% 14.58/2.25    sK2 != sK4 | sK1 != sK3),
% 14.58/2.25    inference(cnf_transformation,[],[f30])).
% 14.58/2.25  fof(f61,plain,(
% 14.58/2.25    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 14.58/2.25    inference(cnf_transformation,[],[f36])).
% 14.58/2.25  fof(f33743,plain,(
% 14.58/2.25    r1_tarski(sK4,sK2) | k1_xboole_0 = sK3),
% 14.58/2.25    inference(superposition,[],[f33710,f50])).
% 14.58/2.25  fof(f33710,plain,(
% 14.58/2.25    ( ! [X0] : (r1_tarski(sK4,k2_xboole_0(sK2,X0)) | k1_xboole_0 = sK3) )),
% 14.58/2.25    inference(resolution,[],[f33008,f6245])).
% 14.58/2.25  fof(f6245,plain,(
% 14.58/2.25    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X0)) | r1_tarski(sK4,X0) | k1_xboole_0 = sK3) )),
% 14.58/2.25    inference(superposition,[],[f77,f45])).
% 14.58/2.25  fof(f33008,plain,(
% 14.58/2.25    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k2_xboole_0(sK2,X0)))) )),
% 14.58/2.25    inference(backward_demodulation,[],[f2377,f33007])).
% 14.58/2.25  fof(f33007,plain,(
% 14.58/2.25    ( ! [X0] : (k2_zfmisc_1(sK3,k2_xboole_0(sK4,X0)) = k2_zfmisc_1(sK3,k2_xboole_0(sK2,X0))) )),
% 14.58/2.25    inference(backward_demodulation,[],[f2302,f32966])).
% 14.58/2.25  fof(f32966,plain,(
% 14.58/2.25    ( ! [X2] : (k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X2)) = k2_zfmisc_1(sK3,k2_xboole_0(sK2,X2))) )),
% 14.58/2.25    inference(superposition,[],[f65,f32872])).
% 14.58/2.25  fof(f2302,plain,(
% 14.58/2.25    ( ! [X0] : (k2_zfmisc_1(sK3,k2_xboole_0(sK4,X0)) = k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X0))) )),
% 14.58/2.25    inference(superposition,[],[f65,f45])).
% 14.58/2.25  fof(f2377,plain,(
% 14.58/2.25    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k2_xboole_0(sK4,X0)))) )),
% 14.58/2.25    inference(superposition,[],[f2322,f45])).
% 14.58/2.25  fof(f32251,plain,(
% 14.58/2.25    ~r1_tarski(sK1,sK3) | sK1 = sK3),
% 14.58/2.25    inference(resolution,[],[f32250,f61])).
% 14.58/2.25  % SZS output end Proof for theBenchmark
% 14.58/2.25  % (10034)------------------------------
% 14.58/2.25  % (10034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.58/2.25  % (10034)Termination reason: Refutation
% 14.58/2.25  
% 14.58/2.25  % (10034)Memory used [KB]: 29423
% 14.58/2.25  % (10034)Time elapsed: 1.813 s
% 14.58/2.25  % (10034)------------------------------
% 14.58/2.25  % (10034)------------------------------
% 14.58/2.26  % (10017)Success in time 1.901 s
%------------------------------------------------------------------------------
