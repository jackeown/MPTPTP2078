%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:59 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  135 (1461 expanded)
%              Number of leaves         :   21 ( 405 expanded)
%              Depth                    :   30
%              Number of atoms          :  331 (5032 expanded)
%              Number of equality atoms :  209 (3005 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1171,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1170,f615])).

fof(f615,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f52,f614])).

fof(f614,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f613,f582])).

fof(f582,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f95,f225,f578])).

fof(f578,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f138,f432])).

fof(f432,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f367,f431])).

fof(f431,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f400,f100])).

fof(f100,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f62,f55])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f400,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f83,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f83,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f367,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f362,f225])).

fof(f362,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f300,f62])).

fof(f300,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f66,f50])).

fof(f50,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34])).

fof(f34,plain,
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

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f138,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(X3,X4))
      | k3_xboole_0(X3,X4) = X3 ) ),
    inference(resolution,[],[f70,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f225,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f219,f141])).

fof(f141,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f140,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f140,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f70,f99])).

fof(f99,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f60,f50])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f219,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f57,f210])).

fof(f210,plain,
    ( sK0 = sK3(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f206,f92])).

fof(f92,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f206,plain,
    ( r2_hidden(sK3(sK1),k1_tarski(sK0))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f189,f50])).

fof(f189,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0),k2_xboole_0(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f158,f155])).

fof(f155,plain,(
    ! [X3] :
      ( k2_xboole_0(k1_tarski(sK3(X3)),X3) = X3
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f119,f57])).

fof(f119,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,X6)
      | k2_xboole_0(k1_tarski(X5),X6) = X6 ) ),
    inference(resolution,[],[f67,f79])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f158,plain,(
    ! [X4,X2,X3] : r2_hidden(X2,k2_xboole_0(k2_xboole_0(k1_tarski(X2),X3),X4)) ),
    inference(resolution,[],[f143,f60])).

fof(f143,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X2),X4),X3)
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f71,f109])).

fof(f109,plain,(
    ! [X2,X1] : r2_hidden(X1,k2_xboole_0(k1_tarski(X1),X2)) ),
    inference(resolution,[],[f78,f60])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f95,plain,
    ( sK1 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(inner_rewriting,[],[f94])).

fof(f94,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f51])).

fof(f51,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f613,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f610])).

fof(f610,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f609,f240])).

fof(f240,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,X1)
      | r1_tarski(sK1,X1)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f79,f225])).

fof(f609,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f603,f252])).

fof(f252,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f233])).

fof(f233,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f53,f225])).

fof(f53,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f603,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f57,f597])).

fof(f597,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f594])).

fof(f594,plain,
    ( k1_xboole_0 = sK1
    | sK0 = sK3(sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f593,f242])).

fof(f242,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | sK0 = X2
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f92,f225])).

fof(f593,plain,
    ( r2_hidden(sK3(sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f589,f252])).

fof(f589,plain,
    ( r2_hidden(sK3(sK2),sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f189,f580])).

fof(f580,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f118,f432])).

fof(f118,plain,(
    ! [X4,X3] : k2_xboole_0(k3_xboole_0(X3,X4),X3) = X3 ),
    inference(resolution,[],[f67,f61])).

fof(f52,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f1170,plain,(
    sK2 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f1154,f55])).

fof(f1154,plain,(
    k1_tarski(sK0) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f650,f1146])).

fof(f1146,plain,(
    ! [X8] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X8) ),
    inference(forward_demodulation,[],[f1125,f54])).

fof(f1125,plain,(
    ! [X8] : k3_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,X8) ),
    inference(backward_demodulation,[],[f293,f1123])).

fof(f1123,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(resolution,[],[f1120,f67])).

fof(f1120,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[],[f1116,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1116,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1115,f131])).

fof(f131,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f93,f130])).

fof(f130,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f127,f54])).

fof(f127,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f65,f58])).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f93,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f1115,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_tarski(X1)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(trivial_inequality_removal,[],[f1114])).

fof(f1114,plain,(
    ! [X1] :
      ( X1 != X1
      | k1_xboole_0 = k1_tarski(X1)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f96,f1112])).

fof(f1112,plain,(
    ! [X0] : sK5(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f1110,f131])).

fof(f1110,plain,(
    ! [X0] :
      ( sK5(X0,k1_xboole_0) = X0
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(condensation,[],[f1109])).

fof(f1109,plain,(
    ! [X8,X7] :
      ( sK5(X7,k1_xboole_0) = X8
      | sK5(X7,k1_xboole_0) = X7
      | k1_xboole_0 = k1_tarski(X7) ) ),
    inference(resolution,[],[f1102,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | sK5(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1102,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | X2 = X3 ) ),
    inference(resolution,[],[f1097,f79])).

fof(f1097,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(k1_tarski(X7),k1_xboole_0)
      | X7 = X8 ) ),
    inference(subsumption_resolution,[],[f1090,f131])).

fof(f1090,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(k1_tarski(X7),k1_xboole_0)
      | k1_xboole_0 = k1_tarski(X7)
      | X7 = X8 ) ),
    inference(superposition,[],[f138,f780])).

fof(f780,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 = k3_xboole_0(k1_tarski(X7),k1_tarski(X8))
      | X7 = X8 ) ),
    inference(forward_demodulation,[],[f765,f54])).

fof(f765,plain,(
    ! [X8,X7] :
      ( k3_xboole_0(k1_tarski(X7),k1_tarski(X8)) = k5_xboole_0(k1_tarski(X7),k1_tarski(X7))
      | X7 = X8 ) ),
    inference(superposition,[],[f441,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f441,plain,(
    ! [X10,X9] : k3_xboole_0(X9,X10) = k5_xboole_0(X9,k4_xboole_0(X9,X10)) ),
    inference(superposition,[],[f431,f65])).

fof(f96,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | k1_tarski(X0) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(inner_rewriting,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f293,plain,(
    ! [X8] : k3_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,k2_xboole_0(k1_xboole_0,X8)) ),
    inference(superposition,[],[f66,f100])).

fof(f650,plain,(
    k1_tarski(sK0) = k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2)) ),
    inference(forward_demodulation,[],[f631,f100])).

fof(f631,plain,(
    k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f444,f614])).

fof(f444,plain,(
    k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f431,f300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:11:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (18302)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (18321)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (18304)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (18305)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (18310)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (18300)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (18310)Refutation not found, incomplete strategy% (18310)------------------------------
% 0.21/0.53  % (18310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18310)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18310)Memory used [KB]: 10618
% 0.21/0.53  % (18310)Time elapsed: 0.115 s
% 0.21/0.53  % (18310)------------------------------
% 0.21/0.53  % (18310)------------------------------
% 0.21/0.53  % (18315)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (18301)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (18322)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (18326)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (18303)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (18317)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (18328)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (18308)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (18307)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (18318)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (18309)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (18313)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (18316)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (18323)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (18319)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (18311)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (18325)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (18311)Refutation not found, incomplete strategy% (18311)------------------------------
% 0.21/0.55  % (18311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18311)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18311)Memory used [KB]: 10618
% 0.21/0.55  % (18311)Time elapsed: 0.148 s
% 0.21/0.55  % (18311)------------------------------
% 0.21/0.55  % (18311)------------------------------
% 0.21/0.55  % (18329)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (18327)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (18312)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (18324)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (18306)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (18314)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.67/0.59  % (18320)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.15/0.66  % (18307)Refutation found. Thanks to Tanya!
% 2.15/0.66  % SZS status Theorem for theBenchmark
% 2.15/0.66  % SZS output start Proof for theBenchmark
% 2.15/0.66  fof(f1171,plain,(
% 2.15/0.66    $false),
% 2.15/0.66    inference(subsumption_resolution,[],[f1170,f615])).
% 2.15/0.66  fof(f615,plain,(
% 2.15/0.66    sK2 != k1_tarski(sK0)),
% 2.15/0.66    inference(subsumption_resolution,[],[f52,f614])).
% 2.15/0.66  fof(f614,plain,(
% 2.15/0.66    k1_xboole_0 = sK1),
% 2.15/0.66    inference(subsumption_resolution,[],[f613,f582])).
% 2.15/0.66  fof(f582,plain,(
% 2.15/0.66    ~r1_tarski(sK1,sK2) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(global_subsumption,[],[f95,f225,f578])).
% 2.15/0.66  fof(f578,plain,(
% 2.15/0.66    ~r1_tarski(sK1,sK2) | sK1 = sK2 | k1_xboole_0 = sK1),
% 2.15/0.66    inference(superposition,[],[f138,f432])).
% 2.15/0.66  fof(f432,plain,(
% 2.15/0.66    sK2 = k3_xboole_0(sK1,sK2) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(backward_demodulation,[],[f367,f431])).
% 2.15/0.66  fof(f431,plain,(
% 2.15/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.15/0.66    inference(forward_demodulation,[],[f400,f100])).
% 2.15/0.66  fof(f100,plain,(
% 2.15/0.66    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.15/0.66    inference(superposition,[],[f62,f55])).
% 2.15/0.66  fof(f55,plain,(
% 2.15/0.66    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.15/0.66    inference(cnf_transformation,[],[f10])).
% 2.15/0.66  fof(f10,axiom,(
% 2.15/0.66    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.15/0.66  fof(f62,plain,(
% 2.15/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f1])).
% 2.15/0.66  fof(f1,axiom,(
% 2.15/0.66    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.15/0.66  fof(f400,plain,(
% 2.15/0.66    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.15/0.66    inference(superposition,[],[f83,f54])).
% 2.15/0.66  fof(f54,plain,(
% 2.15/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f13])).
% 2.15/0.66  fof(f13,axiom,(
% 2.15/0.66    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.15/0.66  fof(f83,plain,(
% 2.15/0.66    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.15/0.66    inference(cnf_transformation,[],[f12])).
% 2.15/0.66  fof(f12,axiom,(
% 2.15/0.66    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.15/0.66  fof(f367,plain,(
% 2.15/0.66    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(superposition,[],[f362,f225])).
% 2.15/0.66  fof(f362,plain,(
% 2.15/0.66    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2))),
% 2.15/0.66    inference(superposition,[],[f300,f62])).
% 2.15/0.66  fof(f300,plain,(
% 2.15/0.66    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 2.15/0.66    inference(superposition,[],[f66,f50])).
% 2.15/0.66  fof(f50,plain,(
% 2.15/0.66    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.15/0.66    inference(cnf_transformation,[],[f35])).
% 2.15/0.66  fof(f35,plain,(
% 2.15/0.66    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.15/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34])).
% 2.15/0.66  fof(f34,plain,(
% 2.15/0.66    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.15/0.66    introduced(choice_axiom,[])).
% 2.15/0.66  fof(f30,plain,(
% 2.15/0.66    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.15/0.66    inference(ennf_transformation,[],[f27])).
% 2.15/0.66  fof(f27,negated_conjecture,(
% 2.15/0.66    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.15/0.66    inference(negated_conjecture,[],[f26])).
% 2.15/0.66  fof(f26,conjecture,(
% 2.15/0.66    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.15/0.66  fof(f66,plain,(
% 2.15/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.15/0.66    inference(cnf_transformation,[],[f14])).
% 2.15/0.66  fof(f14,axiom,(
% 2.15/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.15/0.66  fof(f138,plain,(
% 2.15/0.66    ( ! [X4,X3] : (~r1_tarski(X3,k3_xboole_0(X3,X4)) | k3_xboole_0(X3,X4) = X3) )),
% 2.15/0.66    inference(resolution,[],[f70,f61])).
% 2.15/0.66  fof(f61,plain,(
% 2.15/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f9])).
% 2.15/0.66  fof(f9,axiom,(
% 2.15/0.66    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.15/0.66  fof(f70,plain,(
% 2.15/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.15/0.66    inference(cnf_transformation,[],[f39])).
% 2.15/0.66  fof(f39,plain,(
% 2.15/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.15/0.66    inference(flattening,[],[f38])).
% 2.15/0.66  fof(f38,plain,(
% 2.15/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.15/0.66    inference(nnf_transformation,[],[f6])).
% 2.15/0.66  fof(f6,axiom,(
% 2.15/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.15/0.66  fof(f225,plain,(
% 2.15/0.66    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(resolution,[],[f219,f141])).
% 2.15/0.66  fof(f141,plain,(
% 2.15/0.66    ~r2_hidden(sK0,sK1) | sK1 = k1_tarski(sK0)),
% 2.15/0.66    inference(resolution,[],[f140,f79])).
% 2.15/0.66  fof(f79,plain,(
% 2.15/0.66    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f48])).
% 2.15/0.66  fof(f48,plain,(
% 2.15/0.66    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.15/0.66    inference(nnf_transformation,[],[f23])).
% 2.15/0.66  fof(f23,axiom,(
% 2.15/0.66    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.15/0.66  fof(f140,plain,(
% 2.15/0.66    ~r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 2.15/0.66    inference(resolution,[],[f70,f99])).
% 2.15/0.66  fof(f99,plain,(
% 2.15/0.66    r1_tarski(sK1,k1_tarski(sK0))),
% 2.15/0.66    inference(superposition,[],[f60,f50])).
% 2.15/0.66  fof(f60,plain,(
% 2.15/0.66    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.15/0.66    inference(cnf_transformation,[],[f11])).
% 2.15/0.66  fof(f11,axiom,(
% 2.15/0.66    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.15/0.66  fof(f219,plain,(
% 2.15/0.66    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(duplicate_literal_removal,[],[f218])).
% 2.15/0.66  fof(f218,plain,(
% 2.15/0.66    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 2.15/0.66    inference(superposition,[],[f57,f210])).
% 2.15/0.66  fof(f210,plain,(
% 2.15/0.66    sK0 = sK3(sK1) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(resolution,[],[f206,f92])).
% 2.15/0.66  fof(f92,plain,(
% 2.15/0.66    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 2.15/0.66    inference(equality_resolution,[],[f74])).
% 2.15/0.66  fof(f74,plain,(
% 2.15/0.66    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.15/0.66    inference(cnf_transformation,[],[f47])).
% 2.15/0.66  fof(f47,plain,(
% 2.15/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.15/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).
% 2.15/0.66  fof(f46,plain,(
% 2.15/0.66    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 2.15/0.66    introduced(choice_axiom,[])).
% 2.15/0.66  fof(f45,plain,(
% 2.15/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.15/0.66    inference(rectify,[],[f44])).
% 2.15/0.66  fof(f44,plain,(
% 2.15/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.15/0.66    inference(nnf_transformation,[],[f15])).
% 2.15/0.66  fof(f15,axiom,(
% 2.15/0.66    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.15/0.66  fof(f206,plain,(
% 2.15/0.66    r2_hidden(sK3(sK1),k1_tarski(sK0)) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(superposition,[],[f189,f50])).
% 2.15/0.66  fof(f189,plain,(
% 2.15/0.66    ( ! [X0,X1] : (r2_hidden(sK3(X0),k2_xboole_0(X0,X1)) | k1_xboole_0 = X0) )),
% 2.15/0.66    inference(superposition,[],[f158,f155])).
% 2.15/0.66  fof(f155,plain,(
% 2.15/0.66    ( ! [X3] : (k2_xboole_0(k1_tarski(sK3(X3)),X3) = X3 | k1_xboole_0 = X3) )),
% 2.15/0.66    inference(resolution,[],[f119,f57])).
% 2.15/0.66  fof(f119,plain,(
% 2.15/0.66    ( ! [X6,X5] : (~r2_hidden(X5,X6) | k2_xboole_0(k1_tarski(X5),X6) = X6) )),
% 2.15/0.66    inference(resolution,[],[f67,f79])).
% 2.15/0.66  fof(f67,plain,(
% 2.15/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.15/0.66    inference(cnf_transformation,[],[f32])).
% 2.15/0.66  fof(f32,plain,(
% 2.15/0.66    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.15/0.66    inference(ennf_transformation,[],[f8])).
% 2.15/0.66  fof(f8,axiom,(
% 2.15/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.15/0.66  fof(f158,plain,(
% 2.15/0.66    ( ! [X4,X2,X3] : (r2_hidden(X2,k2_xboole_0(k2_xboole_0(k1_tarski(X2),X3),X4))) )),
% 2.15/0.66    inference(resolution,[],[f143,f60])).
% 2.15/0.66  fof(f143,plain,(
% 2.15/0.66    ( ! [X4,X2,X3] : (~r1_tarski(k2_xboole_0(k1_tarski(X2),X4),X3) | r2_hidden(X2,X3)) )),
% 2.15/0.66    inference(resolution,[],[f71,f109])).
% 2.15/0.66  fof(f109,plain,(
% 2.15/0.66    ( ! [X2,X1] : (r2_hidden(X1,k2_xboole_0(k1_tarski(X1),X2))) )),
% 2.15/0.66    inference(resolution,[],[f78,f60])).
% 2.15/0.66  fof(f78,plain,(
% 2.15/0.66    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f48])).
% 2.15/0.66  fof(f71,plain,(
% 2.15/0.66    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f43])).
% 2.15/0.66  fof(f43,plain,(
% 2.15/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.15/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).
% 2.15/0.66  fof(f42,plain,(
% 2.15/0.66    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.15/0.66    introduced(choice_axiom,[])).
% 2.15/0.66  fof(f41,plain,(
% 2.15/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.15/0.66    inference(rectify,[],[f40])).
% 2.15/0.66  fof(f40,plain,(
% 2.15/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.15/0.66    inference(nnf_transformation,[],[f33])).
% 2.15/0.66  fof(f33,plain,(
% 2.15/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.15/0.66    inference(ennf_transformation,[],[f2])).
% 2.15/0.66  fof(f2,axiom,(
% 2.15/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.15/0.66  fof(f57,plain,(
% 2.15/0.66    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.15/0.66    inference(cnf_transformation,[],[f37])).
% 2.15/0.66  fof(f37,plain,(
% 2.15/0.66    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.15/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f36])).
% 2.15/0.66  fof(f36,plain,(
% 2.15/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.15/0.66    introduced(choice_axiom,[])).
% 2.15/0.66  fof(f31,plain,(
% 2.15/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.15/0.66    inference(ennf_transformation,[],[f5])).
% 2.15/0.66  fof(f5,axiom,(
% 2.15/0.66    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.15/0.66  fof(f95,plain,(
% 2.15/0.66    sK1 != sK2 | sK1 != k1_tarski(sK0)),
% 2.15/0.66    inference(inner_rewriting,[],[f94])).
% 2.15/0.66  fof(f94,plain,(
% 2.15/0.66    sK2 != k1_tarski(sK0) | sK1 != sK2),
% 2.15/0.66    inference(inner_rewriting,[],[f51])).
% 2.15/0.66  fof(f51,plain,(
% 2.15/0.66    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.15/0.66    inference(cnf_transformation,[],[f35])).
% 2.15/0.66  fof(f613,plain,(
% 2.15/0.66    k1_xboole_0 = sK1 | r1_tarski(sK1,sK2)),
% 2.15/0.66    inference(duplicate_literal_removal,[],[f610])).
% 2.15/0.66  fof(f610,plain,(
% 2.15/0.66    k1_xboole_0 = sK1 | r1_tarski(sK1,sK2) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(resolution,[],[f609,f240])).
% 2.15/0.66  fof(f240,plain,(
% 2.15/0.66    ( ! [X1] : (~r2_hidden(sK0,X1) | r1_tarski(sK1,X1) | k1_xboole_0 = sK1) )),
% 2.15/0.66    inference(superposition,[],[f79,f225])).
% 2.15/0.66  fof(f609,plain,(
% 2.15/0.66    r2_hidden(sK0,sK2) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(subsumption_resolution,[],[f603,f252])).
% 2.15/0.66  fof(f252,plain,(
% 2.15/0.66    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.15/0.66    inference(trivial_inequality_removal,[],[f233])).
% 2.15/0.66  fof(f233,plain,(
% 2.15/0.66    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.15/0.66    inference(superposition,[],[f53,f225])).
% 2.15/0.66  fof(f53,plain,(
% 2.15/0.66    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.15/0.66    inference(cnf_transformation,[],[f35])).
% 2.15/0.66  fof(f603,plain,(
% 2.15/0.66    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 2.15/0.66    inference(superposition,[],[f57,f597])).
% 2.15/0.66  fof(f597,plain,(
% 2.15/0.66    sK0 = sK3(sK2) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(duplicate_literal_removal,[],[f594])).
% 2.15/0.66  fof(f594,plain,(
% 2.15/0.66    k1_xboole_0 = sK1 | sK0 = sK3(sK2) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(resolution,[],[f593,f242])).
% 2.15/0.66  fof(f242,plain,(
% 2.15/0.66    ( ! [X2] : (~r2_hidden(X2,sK1) | sK0 = X2 | k1_xboole_0 = sK1) )),
% 2.15/0.66    inference(superposition,[],[f92,f225])).
% 2.15/0.66  fof(f593,plain,(
% 2.15/0.66    r2_hidden(sK3(sK2),sK1) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(subsumption_resolution,[],[f589,f252])).
% 2.15/0.66  fof(f589,plain,(
% 2.15/0.66    r2_hidden(sK3(sK2),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 2.15/0.66    inference(superposition,[],[f189,f580])).
% 2.15/0.66  fof(f580,plain,(
% 2.15/0.66    sK1 = k2_xboole_0(sK2,sK1) | k1_xboole_0 = sK1),
% 2.15/0.66    inference(superposition,[],[f118,f432])).
% 2.15/0.66  fof(f118,plain,(
% 2.15/0.66    ( ! [X4,X3] : (k2_xboole_0(k3_xboole_0(X3,X4),X3) = X3) )),
% 2.15/0.66    inference(resolution,[],[f67,f61])).
% 2.15/0.66  fof(f52,plain,(
% 2.15/0.66    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.15/0.66    inference(cnf_transformation,[],[f35])).
% 2.15/0.66  fof(f1170,plain,(
% 2.15/0.66    sK2 = k1_tarski(sK0)),
% 2.15/0.66    inference(forward_demodulation,[],[f1154,f55])).
% 2.15/0.66  fof(f1154,plain,(
% 2.15/0.66    k1_tarski(sK0) = k5_xboole_0(sK2,k1_xboole_0)),
% 2.15/0.66    inference(backward_demodulation,[],[f650,f1146])).
% 2.15/0.66  fof(f1146,plain,(
% 2.15/0.66    ( ! [X8] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X8)) )),
% 2.15/0.66    inference(forward_demodulation,[],[f1125,f54])).
% 2.15/0.66  fof(f1125,plain,(
% 2.15/0.66    ( ! [X8] : (k3_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,X8)) )),
% 2.15/0.66    inference(backward_demodulation,[],[f293,f1123])).
% 2.15/0.66  fof(f1123,plain,(
% 2.15/0.66    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.15/0.66    inference(resolution,[],[f1120,f67])).
% 2.15/0.66  fof(f1120,plain,(
% 2.15/0.66    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 2.15/0.66    inference(resolution,[],[f1116,f72])).
% 2.15/0.66  fof(f72,plain,(
% 2.15/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f43])).
% 2.15/0.66  fof(f1116,plain,(
% 2.15/0.66    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 2.15/0.66    inference(subsumption_resolution,[],[f1115,f131])).
% 2.15/0.66  fof(f131,plain,(
% 2.15/0.66    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 2.15/0.66    inference(backward_demodulation,[],[f93,f130])).
% 2.15/0.66  fof(f130,plain,(
% 2.15/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.15/0.66    inference(forward_demodulation,[],[f127,f54])).
% 2.15/0.66  fof(f127,plain,(
% 2.15/0.66    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 2.15/0.66    inference(superposition,[],[f65,f58])).
% 2.15/0.66  fof(f58,plain,(
% 2.15/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.15/0.66    inference(cnf_transformation,[],[f28])).
% 2.15/0.66  fof(f28,plain,(
% 2.15/0.66    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.15/0.66    inference(rectify,[],[f4])).
% 2.15/0.66  fof(f4,axiom,(
% 2.15/0.66    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.15/0.66  fof(f65,plain,(
% 2.15/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.15/0.66    inference(cnf_transformation,[],[f7])).
% 2.15/0.66  fof(f7,axiom,(
% 2.15/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.15/0.66  fof(f93,plain,(
% 2.15/0.66    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 2.15/0.66    inference(equality_resolution,[],[f80])).
% 2.15/0.66  fof(f80,plain,(
% 2.15/0.66    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.15/0.66    inference(cnf_transformation,[],[f49])).
% 2.15/0.66  fof(f49,plain,(
% 2.15/0.66    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 2.15/0.66    inference(nnf_transformation,[],[f25])).
% 2.15/0.66  fof(f25,axiom,(
% 2.15/0.66    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 2.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 2.15/0.66  fof(f1115,plain,(
% 2.15/0.66    ( ! [X1] : (k1_xboole_0 = k1_tarski(X1) | ~r2_hidden(X1,k1_xboole_0)) )),
% 2.15/0.66    inference(trivial_inequality_removal,[],[f1114])).
% 2.15/0.66  fof(f1114,plain,(
% 2.15/0.66    ( ! [X1] : (X1 != X1 | k1_xboole_0 = k1_tarski(X1) | ~r2_hidden(X1,k1_xboole_0)) )),
% 2.15/0.66    inference(superposition,[],[f96,f1112])).
% 2.15/0.66  fof(f1112,plain,(
% 2.15/0.66    ( ! [X0] : (sK5(X0,k1_xboole_0) = X0) )),
% 2.15/0.66    inference(subsumption_resolution,[],[f1110,f131])).
% 2.15/0.66  fof(f1110,plain,(
% 2.15/0.66    ( ! [X0] : (sK5(X0,k1_xboole_0) = X0 | k1_xboole_0 = k1_tarski(X0)) )),
% 2.15/0.66    inference(condensation,[],[f1109])).
% 2.15/0.66  fof(f1109,plain,(
% 2.15/0.66    ( ! [X8,X7] : (sK5(X7,k1_xboole_0) = X8 | sK5(X7,k1_xboole_0) = X7 | k1_xboole_0 = k1_tarski(X7)) )),
% 2.15/0.66    inference(resolution,[],[f1102,f76])).
% 2.15/0.66  fof(f76,plain,(
% 2.15/0.66    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | sK5(X0,X1) = X0 | k1_tarski(X0) = X1) )),
% 2.15/0.66    inference(cnf_transformation,[],[f47])).
% 2.15/0.66  fof(f1102,plain,(
% 2.15/0.66    ( ! [X2,X3] : (~r2_hidden(X2,k1_xboole_0) | X2 = X3) )),
% 2.15/0.66    inference(resolution,[],[f1097,f79])).
% 2.15/0.66  fof(f1097,plain,(
% 2.15/0.66    ( ! [X8,X7] : (~r1_tarski(k1_tarski(X7),k1_xboole_0) | X7 = X8) )),
% 2.15/0.66    inference(subsumption_resolution,[],[f1090,f131])).
% 2.15/0.66  fof(f1090,plain,(
% 2.15/0.66    ( ! [X8,X7] : (~r1_tarski(k1_tarski(X7),k1_xboole_0) | k1_xboole_0 = k1_tarski(X7) | X7 = X8) )),
% 2.15/0.66    inference(superposition,[],[f138,f780])).
% 2.15/0.66  fof(f780,plain,(
% 2.15/0.66    ( ! [X8,X7] : (k1_xboole_0 = k3_xboole_0(k1_tarski(X7),k1_tarski(X8)) | X7 = X8) )),
% 2.15/0.66    inference(forward_demodulation,[],[f765,f54])).
% 2.15/0.66  fof(f765,plain,(
% 2.15/0.66    ( ! [X8,X7] : (k3_xboole_0(k1_tarski(X7),k1_tarski(X8)) = k5_xboole_0(k1_tarski(X7),k1_tarski(X7)) | X7 = X8) )),
% 2.15/0.66    inference(superposition,[],[f441,f81])).
% 2.15/0.66  fof(f81,plain,(
% 2.15/0.66    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.15/0.66    inference(cnf_transformation,[],[f49])).
% 2.15/0.66  fof(f441,plain,(
% 2.15/0.66    ( ! [X10,X9] : (k3_xboole_0(X9,X10) = k5_xboole_0(X9,k4_xboole_0(X9,X10))) )),
% 2.15/0.66    inference(superposition,[],[f431,f65])).
% 2.15/0.66  fof(f96,plain,(
% 2.15/0.66    ( ! [X0,X1] : (sK5(X0,X1) != X0 | k1_tarski(X0) = X1 | ~r2_hidden(X0,X1)) )),
% 2.15/0.66    inference(inner_rewriting,[],[f77])).
% 2.15/0.66  fof(f77,plain,(
% 2.15/0.66    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f47])).
% 2.15/0.66  fof(f293,plain,(
% 2.15/0.66    ( ! [X8] : (k3_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,k2_xboole_0(k1_xboole_0,X8))) )),
% 2.15/0.66    inference(superposition,[],[f66,f100])).
% 2.15/0.66  fof(f650,plain,(
% 2.15/0.66    k1_tarski(sK0) = k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2))),
% 2.15/0.66    inference(forward_demodulation,[],[f631,f100])).
% 2.15/0.66  fof(f631,plain,(
% 2.15/0.66    k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k1_xboole_0,sK2))),
% 2.15/0.66    inference(backward_demodulation,[],[f444,f614])).
% 2.15/0.66  fof(f444,plain,(
% 2.15/0.66    k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))),
% 2.15/0.66    inference(superposition,[],[f431,f300])).
% 2.15/0.66  % SZS output end Proof for theBenchmark
% 2.15/0.66  % (18307)------------------------------
% 2.15/0.66  % (18307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.66  % (18307)Termination reason: Refutation
% 2.15/0.66  
% 2.15/0.66  % (18307)Memory used [KB]: 7164
% 2.15/0.66  % (18307)Time elapsed: 0.222 s
% 2.15/0.66  % (18307)------------------------------
% 2.15/0.66  % (18307)------------------------------
% 2.15/0.68  % (18299)Success in time 0.321 s
%------------------------------------------------------------------------------
