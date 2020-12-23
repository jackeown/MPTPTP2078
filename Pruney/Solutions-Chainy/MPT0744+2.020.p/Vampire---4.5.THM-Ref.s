%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 440 expanded)
%              Number of leaves         :   14 ( 123 expanded)
%              Depth                    :   30
%              Number of atoms          :  328 (1647 expanded)
%              Number of equality atoms :   52 ( 261 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f361,plain,(
    $false ),
    inference(resolution,[],[f358,f34])).

fof(f34,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK0,X1)
            | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK0,X1)
            | r2_hidden(sK0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK0,X1)
          | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK0,X1)
          | r2_hidden(sK0,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK0,sK1)
        | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
      & ( r1_ordinal1(sK0,sK1)
        | r2_hidden(sK0,k1_ordinal1(sK1)) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f358,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f356,f76])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f356,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f355])).

fof(f355,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f350,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f350,plain,(
    ~ r1_ordinal1(sK0,sK0) ),
    inference(resolution,[],[f334,f75])).

fof(f75,plain,(
    ! [X1] : r2_hidden(X1,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1))))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f60,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f51,f58,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f334,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | ~ r1_ordinal1(sK0,sK0) ),
    inference(forward_demodulation,[],[f302,f300])).

fof(f300,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f299,f34])).

fof(f299,plain,
    ( ~ v3_ordinal1(sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f278,f35])).

fof(f35,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f278,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f274,f101])).

fof(f101,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f95,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f95,plain,
    ( r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f91,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f91,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f73,f61])).

fof(f61,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK1,sK1,sK1))))
    | ~ r1_ordinal1(sK0,sK1) ),
    inference(definition_unfolding,[],[f37,f60])).

fof(f37,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f274,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,
    ( ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f270,f40])).

fof(f270,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f266,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f266,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f85,f222])).

fof(f222,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f111,f62])).

fof(f62,plain,
    ( r2_hidden(sK0,k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK1,sK1,sK1))))
    | r1_ordinal1(sK0,sK1) ),
    inference(definition_unfolding,[],[f36,f60])).

fof(f36,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f111,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK1,sK1,sK1))))
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f71,f101])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f47,f60])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(resolution,[],[f38,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f302,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | ~ r2_hidden(sK0,k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK1,sK1,sK1)))) ),
    inference(backward_demodulation,[],[f61,f300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (19334)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (19336)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (19361)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (19340)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (19337)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (19333)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (19333)Refutation not found, incomplete strategy% (19333)------------------------------
% 0.21/0.54  % (19333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19333)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19333)Memory used [KB]: 1663
% 0.21/0.54  % (19333)Time elapsed: 0.133 s
% 0.21/0.54  % (19333)------------------------------
% 0.21/0.54  % (19333)------------------------------
% 0.21/0.54  % (19332)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (19354)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (19357)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (19337)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(resolution,[],[f358,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    v3_ordinal1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.54    inference(negated_conjecture,[],[f11])).
% 0.21/0.54  fof(f11,conjecture,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    ~v3_ordinal1(sK0)),
% 0.21/0.54    inference(resolution,[],[f356,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    ~r1_tarski(sK0,sK0) | ~v3_ordinal1(sK0)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f355])).
% 0.21/0.54  fof(f355,plain,(
% 0.21/0.54    ~r1_tarski(sK0,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK0)),
% 0.21/0.54    inference(resolution,[],[f350,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.54  fof(f350,plain,(
% 0.21/0.54    ~r1_ordinal1(sK0,sK0)),
% 0.21/0.54    inference(resolution,[],[f334,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(X1,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1))))) )),
% 0.21/0.54    inference(equality_resolution,[],[f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) | X0 != X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f49,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f51,f58,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f56,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f55,f57])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.54  fof(f334,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | ~r1_ordinal1(sK0,sK0)),
% 0.21/0.54    inference(forward_demodulation,[],[f302,f300])).
% 0.21/0.54  fof(f300,plain,(
% 0.21/0.54    sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f299,f34])).
% 0.21/0.54  fof(f299,plain,(
% 0.21/0.54    ~v3_ordinal1(sK0) | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f278,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    v3_ordinal1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f278,plain,(
% 0.21/0.54    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = sK1),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f275])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.54    inference(resolution,[],[f274,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f95,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    r2_hidden(sK1,sK0) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.54    inference(resolution,[],[f91,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f73,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK1,sK1,sK1)))) | ~r1_ordinal1(sK0,sK1)),
% 0.21/0.54    inference(definition_unfolding,[],[f37,f60])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f42,f58])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(rectify,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(flattening,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.54  fof(f274,plain,(
% 0.21/0.54    r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f271])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    ~v3_ordinal1(sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.54    inference(resolution,[],[f270,f40])).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    ~r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1) | sK0 = sK1 | ~v3_ordinal1(sK0)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f269])).
% 0.21/0.54  fof(f269,plain,(
% 0.21/0.54    ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK0 = sK1 | ~r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.54    inference(resolution,[],[f266,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f266,plain,(
% 0.21/0.54    ~r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK0 = sK1),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f265])).
% 0.21/0.54  fof(f265,plain,(
% 0.21/0.54    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~r1_tarski(sK1,sK0) | sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f85,f222])).
% 0.21/0.54  fof(f222,plain,(
% 0.21/0.54    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f111,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    r2_hidden(sK0,k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK1,sK1,sK1)))) | r1_ordinal1(sK0,sK1)),
% 0.21/0.54    inference(definition_unfolding,[],[f36,f60])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK1,sK1,sK1)))) | sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.54    inference(resolution,[],[f71,f101])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1))))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f47,f60])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.54    inference(resolution,[],[f38,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f302,plain,(
% 0.21/0.54    ~r1_ordinal1(sK0,sK0) | ~r2_hidden(sK0,k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK1,sK1,sK1))))),
% 0.21/0.54    inference(backward_demodulation,[],[f61,f300])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (19337)------------------------------
% 0.21/0.54  % (19337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19337)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (19337)Memory used [KB]: 1918
% 0.21/0.54  % (19337)Time elapsed: 0.128 s
% 0.21/0.54  % (19337)------------------------------
% 0.21/0.54  % (19337)------------------------------
% 0.21/0.54  % (19348)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (19331)Success in time 0.18 s
%------------------------------------------------------------------------------
