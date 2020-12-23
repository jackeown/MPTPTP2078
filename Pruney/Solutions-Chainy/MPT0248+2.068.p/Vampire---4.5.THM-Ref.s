%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:59 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  112 (1365 expanded)
%              Number of leaves         :   20 ( 379 expanded)
%              Depth                    :   26
%              Number of atoms          :  283 (4783 expanded)
%              Number of equality atoms :  174 (2846 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f659,plain,(
    $false ),
    inference(subsumption_resolution,[],[f658,f636])).

fof(f636,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f53,f635])).

fof(f635,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f634,f607])).

fof(f607,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f606])).

fof(f606,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f603,f272])).

fof(f272,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | ~ r2_hidden(sK0,X1)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f80,f257])).

fof(f257,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f251,f161])).

fof(f161,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f160,f80])).

fof(f160,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f71,f99])).

fof(f99,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f61,f51])).

fof(f51,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35])).

fof(f35,plain,
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

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f251,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f58,f242])).

fof(f242,plain,
    ( sK0 = sK3(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f238,f93])).

fof(f93,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).

fof(f47,plain,(
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

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f238,plain,
    ( r2_hidden(sK3(sK1),k1_tarski(sK0))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f218,f51])).

fof(f218,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0),k2_xboole_0(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f180,f177])).

fof(f177,plain,(
    ! [X3] :
      ( k2_xboole_0(k1_tarski(sK3(X3)),X3) = X3
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f119,f58])).

fof(f119,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | k2_xboole_0(k1_tarski(X3),X4) = X4 ) ),
    inference(resolution,[],[f68,f80])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f180,plain,(
    ! [X4,X2,X3] : r2_hidden(X2,k2_xboole_0(k2_xboole_0(k1_tarski(X2),X3),X4)) ),
    inference(resolution,[],[f163,f61])).

fof(f163,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X2),X4),X3)
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f72,f109])).

fof(f109,plain,(
    ! [X2,X1] : r2_hidden(X1,k2_xboole_0(k1_tarski(X1),X2)) ),
    inference(resolution,[],[f79,f61])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f603,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f96,f257,f598])).

fof(f598,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f158,f442])).

fof(f442,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f392,f441])).

fof(f441,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f416,f100])).

fof(f100,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f62,f56])).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f416,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f84,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f84,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f392,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f387,f257])).

fof(f387,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f305,f62])).

fof(f305,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f67,f51])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f158,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(X3,X4))
      | k3_xboole_0(X3,X4) = X3 ) ),
    inference(resolution,[],[f71,f136])).

fof(f136,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f61,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f96,plain,
    ( sK1 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(inner_rewriting,[],[f95])).

fof(f95,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f52])).

fof(f52,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f634,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f628,f284])).

fof(f284,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f265])).

fof(f265,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f54,f257])).

fof(f54,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f628,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f58,f622])).

fof(f622,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f619])).

fof(f619,plain,
    ( k1_xboole_0 = sK1
    | sK0 = sK3(sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f618,f274])).

fof(f274,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | sK0 = X2
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f93,f257])).

fof(f618,plain,
    ( r2_hidden(sK3(sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f614,f284])).

fof(f614,plain,
    ( r2_hidden(sK3(sK2),sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f218,f599])).

fof(f599,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f139,f442])).

fof(f139,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f136,f68])).

fof(f53,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f658,plain,(
    sK2 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f637,f321])).

fof(f321,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f139,f310])).

fof(f310,plain,(
    ! [X7] : k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0) ),
    inference(forward_demodulation,[],[f309,f55])).

fof(f309,plain,(
    ! [X7] : k3_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X7,X7) ),
    inference(forward_demodulation,[],[f296,f137])).

fof(f137,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f133,f127])).

fof(f127,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f124,f55])).

fof(f124,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f65,f59])).

fof(f59,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f133,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f66,f59])).

fof(f296,plain,(
    ! [X7] : k3_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X7,k2_xboole_0(X7,k1_xboole_0)) ),
    inference(superposition,[],[f67,f56])).

fof(f637,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f51,f635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (29367)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (29360)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (29362)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (29382)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (29359)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (29363)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (29361)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (29365)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (29374)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (29385)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (29364)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (29383)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (29387)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (29381)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (29378)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (29366)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (29377)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (29380)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (29379)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (29373)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (29370)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (29371)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (29375)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (29384)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (29386)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (29369)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.53/0.56  % (29369)Refutation not found, incomplete strategy% (29369)------------------------------
% 1.53/0.56  % (29369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (29369)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (29369)Memory used [KB]: 10618
% 1.53/0.56  % (29369)Time elapsed: 0.148 s
% 1.53/0.56  % (29369)------------------------------
% 1.53/0.56  % (29369)------------------------------
% 1.53/0.56  % (29372)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.53/0.56  % (29368)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.53/0.56  % (29388)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.56  % (29376)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.69/0.60  % (29366)Refutation found. Thanks to Tanya!
% 1.69/0.60  % SZS status Theorem for theBenchmark
% 1.69/0.60  % SZS output start Proof for theBenchmark
% 1.69/0.60  fof(f659,plain,(
% 1.69/0.60    $false),
% 1.69/0.60    inference(subsumption_resolution,[],[f658,f636])).
% 1.69/0.60  fof(f636,plain,(
% 1.69/0.60    sK2 != k1_tarski(sK0)),
% 1.69/0.60    inference(subsumption_resolution,[],[f53,f635])).
% 1.69/0.60  fof(f635,plain,(
% 1.69/0.60    k1_xboole_0 = sK1),
% 1.69/0.60    inference(subsumption_resolution,[],[f634,f607])).
% 1.69/0.60  fof(f607,plain,(
% 1.69/0.60    ~r2_hidden(sK0,sK2) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(duplicate_literal_removal,[],[f606])).
% 1.69/0.60  fof(f606,plain,(
% 1.69/0.60    k1_xboole_0 = sK1 | ~r2_hidden(sK0,sK2) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(resolution,[],[f603,f272])).
% 1.69/0.60  fof(f272,plain,(
% 1.69/0.60    ( ! [X1] : (r1_tarski(sK1,X1) | ~r2_hidden(sK0,X1) | k1_xboole_0 = sK1) )),
% 1.69/0.60    inference(superposition,[],[f80,f257])).
% 1.69/0.60  fof(f257,plain,(
% 1.69/0.60    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(resolution,[],[f251,f161])).
% 1.69/0.60  fof(f161,plain,(
% 1.69/0.60    ~r2_hidden(sK0,sK1) | sK1 = k1_tarski(sK0)),
% 1.69/0.60    inference(resolution,[],[f160,f80])).
% 1.69/0.60  fof(f160,plain,(
% 1.69/0.60    ~r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 1.69/0.60    inference(resolution,[],[f71,f99])).
% 1.69/0.60  fof(f99,plain,(
% 1.69/0.60    r1_tarski(sK1,k1_tarski(sK0))),
% 1.69/0.60    inference(superposition,[],[f61,f51])).
% 1.69/0.60  fof(f51,plain,(
% 1.69/0.60    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.69/0.60    inference(cnf_transformation,[],[f36])).
% 1.69/0.60  fof(f36,plain,(
% 1.69/0.60    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.69/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35])).
% 1.69/0.60  fof(f35,plain,(
% 1.69/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.69/0.60    introduced(choice_axiom,[])).
% 1.69/0.60  fof(f31,plain,(
% 1.69/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.69/0.60    inference(ennf_transformation,[],[f28])).
% 1.69/0.60  fof(f28,negated_conjecture,(
% 1.69/0.60    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.69/0.60    inference(negated_conjecture,[],[f27])).
% 1.69/0.60  fof(f27,conjecture,(
% 1.69/0.60    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.69/0.60  fof(f61,plain,(
% 1.69/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.69/0.60    inference(cnf_transformation,[],[f12])).
% 1.69/0.60  fof(f12,axiom,(
% 1.69/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.69/0.60  fof(f71,plain,(
% 1.69/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.69/0.60    inference(cnf_transformation,[],[f40])).
% 1.69/0.60  fof(f40,plain,(
% 1.69/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.60    inference(flattening,[],[f39])).
% 1.69/0.60  fof(f39,plain,(
% 1.69/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.60    inference(nnf_transformation,[],[f7])).
% 1.69/0.60  fof(f7,axiom,(
% 1.69/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.69/0.60  fof(f251,plain,(
% 1.69/0.60    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(duplicate_literal_removal,[],[f250])).
% 1.69/0.60  fof(f250,plain,(
% 1.69/0.60    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.69/0.60    inference(superposition,[],[f58,f242])).
% 1.69/0.60  fof(f242,plain,(
% 1.69/0.60    sK0 = sK3(sK1) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(resolution,[],[f238,f93])).
% 1.69/0.60  fof(f93,plain,(
% 1.69/0.60    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.69/0.60    inference(equality_resolution,[],[f75])).
% 1.69/0.60  fof(f75,plain,(
% 1.69/0.60    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.69/0.60    inference(cnf_transformation,[],[f48])).
% 1.69/0.60  fof(f48,plain,(
% 1.69/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.69/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).
% 1.69/0.60  fof(f47,plain,(
% 1.69/0.60    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.69/0.60    introduced(choice_axiom,[])).
% 1.69/0.60  fof(f46,plain,(
% 1.69/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.69/0.60    inference(rectify,[],[f45])).
% 1.69/0.60  fof(f45,plain,(
% 1.69/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.69/0.60    inference(nnf_transformation,[],[f16])).
% 1.69/0.60  fof(f16,axiom,(
% 1.69/0.60    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.69/0.60  fof(f238,plain,(
% 1.69/0.60    r2_hidden(sK3(sK1),k1_tarski(sK0)) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(superposition,[],[f218,f51])).
% 1.69/0.60  fof(f218,plain,(
% 1.69/0.60    ( ! [X0,X1] : (r2_hidden(sK3(X0),k2_xboole_0(X0,X1)) | k1_xboole_0 = X0) )),
% 1.69/0.60    inference(superposition,[],[f180,f177])).
% 1.69/0.60  fof(f177,plain,(
% 1.69/0.60    ( ! [X3] : (k2_xboole_0(k1_tarski(sK3(X3)),X3) = X3 | k1_xboole_0 = X3) )),
% 1.69/0.60    inference(resolution,[],[f119,f58])).
% 1.69/0.60  fof(f119,plain,(
% 1.69/0.60    ( ! [X4,X3] : (~r2_hidden(X3,X4) | k2_xboole_0(k1_tarski(X3),X4) = X4) )),
% 1.69/0.60    inference(resolution,[],[f68,f80])).
% 1.69/0.60  fof(f68,plain,(
% 1.69/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.69/0.60    inference(cnf_transformation,[],[f33])).
% 1.69/0.60  fof(f33,plain,(
% 1.69/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.69/0.60    inference(ennf_transformation,[],[f9])).
% 1.69/0.60  fof(f9,axiom,(
% 1.69/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.69/0.60  fof(f180,plain,(
% 1.69/0.60    ( ! [X4,X2,X3] : (r2_hidden(X2,k2_xboole_0(k2_xboole_0(k1_tarski(X2),X3),X4))) )),
% 1.69/0.60    inference(resolution,[],[f163,f61])).
% 1.69/0.60  fof(f163,plain,(
% 1.69/0.60    ( ! [X4,X2,X3] : (~r1_tarski(k2_xboole_0(k1_tarski(X2),X4),X3) | r2_hidden(X2,X3)) )),
% 1.69/0.60    inference(resolution,[],[f72,f109])).
% 1.69/0.60  fof(f109,plain,(
% 1.69/0.60    ( ! [X2,X1] : (r2_hidden(X1,k2_xboole_0(k1_tarski(X1),X2))) )),
% 1.69/0.60    inference(resolution,[],[f79,f61])).
% 1.69/0.60  fof(f79,plain,(
% 1.69/0.60    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f49])).
% 1.69/0.60  fof(f49,plain,(
% 1.69/0.60    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.69/0.60    inference(nnf_transformation,[],[f24])).
% 1.69/0.60  fof(f24,axiom,(
% 1.69/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.69/0.60  fof(f72,plain,(
% 1.69/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f44])).
% 1.69/0.60  fof(f44,plain,(
% 1.69/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.69/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 1.69/0.60  fof(f43,plain,(
% 1.69/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.69/0.60    introduced(choice_axiom,[])).
% 1.69/0.60  fof(f42,plain,(
% 1.69/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.69/0.60    inference(rectify,[],[f41])).
% 1.69/0.60  fof(f41,plain,(
% 1.69/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.69/0.60    inference(nnf_transformation,[],[f34])).
% 1.69/0.60  fof(f34,plain,(
% 1.69/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.69/0.60    inference(ennf_transformation,[],[f3])).
% 1.69/0.60  fof(f3,axiom,(
% 1.69/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.69/0.60  fof(f58,plain,(
% 1.69/0.60    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.69/0.60    inference(cnf_transformation,[],[f38])).
% 1.69/0.60  fof(f38,plain,(
% 1.69/0.60    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.69/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f37])).
% 1.69/0.60  fof(f37,plain,(
% 1.69/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.69/0.60    introduced(choice_axiom,[])).
% 1.69/0.60  fof(f32,plain,(
% 1.69/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.69/0.60    inference(ennf_transformation,[],[f6])).
% 1.69/0.60  fof(f6,axiom,(
% 1.69/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.69/0.60  fof(f80,plain,(
% 1.69/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f49])).
% 1.69/0.60  fof(f603,plain,(
% 1.69/0.60    ~r1_tarski(sK1,sK2) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(global_subsumption,[],[f96,f257,f598])).
% 1.69/0.60  fof(f598,plain,(
% 1.69/0.60    ~r1_tarski(sK1,sK2) | sK1 = sK2 | k1_xboole_0 = sK1),
% 1.69/0.60    inference(superposition,[],[f158,f442])).
% 1.69/0.60  fof(f442,plain,(
% 1.69/0.60    sK2 = k3_xboole_0(sK1,sK2) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(backward_demodulation,[],[f392,f441])).
% 1.69/0.60  fof(f441,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.69/0.60    inference(forward_demodulation,[],[f416,f100])).
% 1.69/0.60  fof(f100,plain,(
% 1.69/0.60    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.69/0.60    inference(superposition,[],[f62,f56])).
% 1.69/0.60  fof(f56,plain,(
% 1.69/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.69/0.60    inference(cnf_transformation,[],[f11])).
% 1.69/0.60  fof(f11,axiom,(
% 1.69/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.69/0.60  fof(f62,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f1])).
% 1.69/0.60  fof(f1,axiom,(
% 1.69/0.60    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.69/0.60  fof(f416,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.69/0.60    inference(superposition,[],[f84,f55])).
% 1.69/0.60  fof(f55,plain,(
% 1.69/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f14])).
% 1.69/0.60  fof(f14,axiom,(
% 1.69/0.60    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.69/0.60  fof(f84,plain,(
% 1.69/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.69/0.60    inference(cnf_transformation,[],[f13])).
% 1.69/0.60  fof(f13,axiom,(
% 1.69/0.60    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.69/0.60  fof(f392,plain,(
% 1.69/0.60    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(superposition,[],[f387,f257])).
% 1.69/0.60  fof(f387,plain,(
% 1.69/0.60    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2))),
% 1.69/0.60    inference(superposition,[],[f305,f62])).
% 1.69/0.60  fof(f305,plain,(
% 1.69/0.60    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 1.69/0.60    inference(superposition,[],[f67,f51])).
% 1.69/0.60  fof(f67,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.69/0.60    inference(cnf_transformation,[],[f15])).
% 1.69/0.60  fof(f15,axiom,(
% 1.69/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.69/0.60  fof(f158,plain,(
% 1.69/0.60    ( ! [X4,X3] : (~r1_tarski(X3,k3_xboole_0(X3,X4)) | k3_xboole_0(X3,X4) = X3) )),
% 1.69/0.60    inference(resolution,[],[f71,f136])).
% 1.69/0.60  fof(f136,plain,(
% 1.69/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.69/0.60    inference(superposition,[],[f61,f66])).
% 1.69/0.60  fof(f66,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.69/0.60    inference(cnf_transformation,[],[f10])).
% 1.69/0.60  fof(f10,axiom,(
% 1.69/0.60    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.69/0.60  fof(f96,plain,(
% 1.69/0.60    sK1 != sK2 | sK1 != k1_tarski(sK0)),
% 1.69/0.60    inference(inner_rewriting,[],[f95])).
% 1.69/0.60  fof(f95,plain,(
% 1.69/0.60    sK2 != k1_tarski(sK0) | sK1 != sK2),
% 1.69/0.60    inference(inner_rewriting,[],[f52])).
% 1.69/0.60  fof(f52,plain,(
% 1.69/0.60    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.69/0.60    inference(cnf_transformation,[],[f36])).
% 1.69/0.60  fof(f634,plain,(
% 1.69/0.60    r2_hidden(sK0,sK2) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(subsumption_resolution,[],[f628,f284])).
% 1.69/0.60  fof(f284,plain,(
% 1.69/0.60    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.69/0.60    inference(trivial_inequality_removal,[],[f265])).
% 1.69/0.60  fof(f265,plain,(
% 1.69/0.60    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.69/0.60    inference(superposition,[],[f54,f257])).
% 1.69/0.60  fof(f54,plain,(
% 1.69/0.60    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.69/0.60    inference(cnf_transformation,[],[f36])).
% 1.69/0.60  fof(f628,plain,(
% 1.69/0.60    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.69/0.60    inference(superposition,[],[f58,f622])).
% 1.69/0.60  fof(f622,plain,(
% 1.69/0.60    sK0 = sK3(sK2) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(duplicate_literal_removal,[],[f619])).
% 1.69/0.60  fof(f619,plain,(
% 1.69/0.60    k1_xboole_0 = sK1 | sK0 = sK3(sK2) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(resolution,[],[f618,f274])).
% 1.69/0.60  fof(f274,plain,(
% 1.69/0.60    ( ! [X2] : (~r2_hidden(X2,sK1) | sK0 = X2 | k1_xboole_0 = sK1) )),
% 1.69/0.60    inference(superposition,[],[f93,f257])).
% 1.69/0.60  fof(f618,plain,(
% 1.69/0.60    r2_hidden(sK3(sK2),sK1) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(subsumption_resolution,[],[f614,f284])).
% 1.69/0.60  fof(f614,plain,(
% 1.69/0.60    r2_hidden(sK3(sK2),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.69/0.60    inference(superposition,[],[f218,f599])).
% 1.69/0.60  fof(f599,plain,(
% 1.69/0.60    sK1 = k2_xboole_0(sK2,sK1) | k1_xboole_0 = sK1),
% 1.69/0.60    inference(superposition,[],[f139,f442])).
% 1.69/0.60  fof(f139,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 1.69/0.60    inference(resolution,[],[f136,f68])).
% 1.69/0.60  fof(f53,plain,(
% 1.69/0.60    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.69/0.60    inference(cnf_transformation,[],[f36])).
% 1.69/0.60  fof(f658,plain,(
% 1.69/0.60    sK2 = k1_tarski(sK0)),
% 1.69/0.60    inference(forward_demodulation,[],[f637,f321])).
% 1.69/0.60  fof(f321,plain,(
% 1.69/0.60    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.69/0.60    inference(superposition,[],[f139,f310])).
% 1.69/0.60  fof(f310,plain,(
% 1.69/0.60    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0)) )),
% 1.69/0.60    inference(forward_demodulation,[],[f309,f55])).
% 1.69/0.60  fof(f309,plain,(
% 1.69/0.60    ( ! [X7] : (k3_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X7,X7)) )),
% 1.69/0.60    inference(forward_demodulation,[],[f296,f137])).
% 1.69/0.60  fof(f137,plain,(
% 1.69/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.69/0.60    inference(forward_demodulation,[],[f133,f127])).
% 1.69/0.60  fof(f127,plain,(
% 1.69/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.69/0.60    inference(forward_demodulation,[],[f124,f55])).
% 1.69/0.60  fof(f124,plain,(
% 1.69/0.60    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 1.69/0.60    inference(superposition,[],[f65,f59])).
% 1.69/0.60  fof(f59,plain,(
% 1.69/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.69/0.60    inference(cnf_transformation,[],[f29])).
% 1.69/0.60  fof(f29,plain,(
% 1.69/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.69/0.60    inference(rectify,[],[f5])).
% 1.69/0.60  fof(f5,axiom,(
% 1.69/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.69/0.60  fof(f65,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.69/0.60    inference(cnf_transformation,[],[f8])).
% 1.69/0.60  fof(f8,axiom,(
% 1.69/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.69/0.60  fof(f133,plain,(
% 1.69/0.60    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.69/0.60    inference(superposition,[],[f66,f59])).
% 1.69/0.60  fof(f296,plain,(
% 1.69/0.60    ( ! [X7] : (k3_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X7,k2_xboole_0(X7,k1_xboole_0))) )),
% 1.69/0.60    inference(superposition,[],[f67,f56])).
% 1.69/0.60  fof(f637,plain,(
% 1.69/0.60    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 1.69/0.60    inference(backward_demodulation,[],[f51,f635])).
% 1.69/0.60  % SZS output end Proof for theBenchmark
% 1.69/0.60  % (29366)------------------------------
% 1.69/0.60  % (29366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.60  % (29366)Termination reason: Refutation
% 1.69/0.60  
% 1.69/0.60  % (29366)Memory used [KB]: 6908
% 1.69/0.60  % (29366)Time elapsed: 0.146 s
% 1.69/0.60  % (29366)------------------------------
% 1.69/0.60  % (29366)------------------------------
% 1.69/0.60  % (29358)Success in time 0.245 s
%------------------------------------------------------------------------------
