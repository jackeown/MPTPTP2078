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
% DateTime   : Thu Dec  3 12:37:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 (3658 expanded)
%              Number of leaves         :   11 (1001 expanded)
%              Depth                    :   39
%              Number of atoms          :  343 (13900 expanded)
%              Number of equality atoms :  156 (6663 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(subsumption_resolution,[],[f142,f62])).

fof(f62,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f142,plain,(
    ~ r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(resolution,[],[f140,f130])).

fof(f130,plain,(
    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f128,f52])).

fof(f52,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f27,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | r1_tarski(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | r1_tarski(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f128,plain,
    ( ~ r2_hidden(sK0,sK2)
    | r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(superposition,[],[f40,f127])).

fof(f127,plain,(
    sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f126,f62])).

fof(f126,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(resolution,[],[f120,f103])).

fof(f103,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f100,f51])).

fof(f51,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f28,f49])).

fof(f28,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f100,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(superposition,[],[f40,f99])).

fof(f99,plain,
    ( sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f98,f62])).

fof(f98,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(resolution,[],[f94,f85])).

fof(f85,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f83,f52])).

fof(f83,plain,
    ( sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2)
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(resolution,[],[f82,f51])).

fof(f82,plain,
    ( ~ r2_hidden(sK1,sK2)
    | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2)
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,
    ( sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f76,f50])).

fof(f50,plain,
    ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f29,f49])).

fof(f29,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    ! [X14,X17,X15,X16] :
      ( r1_tarski(k5_enumset1(X15,X15,X15,X15,X15,X14,X16),X17)
      | sK4(k5_enumset1(X15,X15,X15,X15,X15,X14,X16),X17) = X15
      | sK4(k5_enumset1(X15,X15,X15,X15,X15,X14,X16),X17) = X16
      | sK4(k5_enumset1(X15,X15,X15,X15,X15,X14,X16),X17) = X14 ) ),
    inference(resolution,[],[f67,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

% (13094)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f67,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f30,f48])).

fof(f30,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(sK1,X1)
      | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
      | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f93,f64])).

fof(f64,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f32,f48])).

fof(f32,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,(
    ! [X1] :
      ( sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
      | ~ r2_hidden(sK1,X1)
      | ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X1] :
      ( sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
      | ~ r2_hidden(sK1,X1)
      | ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
      | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
      | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ) ),
    inference(resolution,[],[f87,f85])).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,sK2)
      | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
      | ~ r2_hidden(sK1,X1)
      | ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(sK0,X2)
      | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ) ),
    inference(resolution,[],[f84,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,sK2)
      | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
      | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
      | ~ r2_hidden(sK1,X0)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f82,f38])).

fof(f120,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(sK1,X1)
      | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f119,f64])).

fof(f119,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,X1)
      | ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,X1)
      | ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
      | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ) ),
    inference(resolution,[],[f113,f103])).

fof(f113,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,sK2)
      | ~ r2_hidden(sK1,X1)
      | ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(sK0,X2)
      | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ) ),
    inference(resolution,[],[f111,f38])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,sK2)
      | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
      | ~ r2_hidden(sK1,X0)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f104,f38])).

fof(f104,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(resolution,[],[f103,f50])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f140,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f138,f64])).

fof(f138,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | ~ r2_hidden(sK1,X1) ) ),
    inference(resolution,[],[f135,f130])).

fof(f135,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,sK2)
      | ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(sK0,X2)
      | ~ r2_hidden(sK1,X1) ) ),
    inference(resolution,[],[f133,f38])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,sK2)
      | ~ r2_hidden(sK1,X0)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f131,f38])).

fof(f131,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f50,f130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (13067)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (13088)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (13067)Refutation not found, incomplete strategy% (13067)------------------------------
% 0.21/0.50  % (13067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13067)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13067)Memory used [KB]: 10618
% 0.21/0.50  % (13067)Time elapsed: 0.095 s
% 0.21/0.50  % (13067)------------------------------
% 0.21/0.50  % (13067)------------------------------
% 0.21/0.50  % (13076)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (13070)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (13069)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (13079)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (13070)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f142,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 0.21/0.52    inference(equality_resolution,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f42,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f43,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f44,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(rectify,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(nnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.52    inference(resolution,[],[f140,f130])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f128,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    r2_hidden(sK0,sK2) | r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.52    inference(definition_unfolding,[],[f27,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f41,f48])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    r2_hidden(sK0,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | r1_tarski(k2_tarski(sK0,sK1),sK2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | r1_tarski(k2_tarski(sK0,sK1),sK2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.53    inference(nnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ~r2_hidden(sK0,sK2) | r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(superposition,[],[f40,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f126,f62])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(resolution,[],[f120,f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f100,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    r2_hidden(sK1,sK2) | r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(definition_unfolding,[],[f28,f49])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    r2_hidden(sK1,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK2) | r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(superposition,[],[f40,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f98,f62])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(resolution,[],[f94,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f83,f52])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK0,sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(resolution,[],[f82,f51])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK2) | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK0,sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f76,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ~r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 0.21/0.53    inference(definition_unfolding,[],[f29,f49])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X14,X17,X15,X16] : (r1_tarski(k5_enumset1(X15,X15,X15,X15,X15,X14,X16),X17) | sK4(k5_enumset1(X15,X15,X15,X15,X15,X14,X16),X17) = X15 | sK4(k5_enumset1(X15,X15,X15,X15,X15,X14,X16),X17) = X16 | sK4(k5_enumset1(X15,X15,X15,X15,X15,X14,X16),X17) = X14) )),
% 0.21/0.53    inference(resolution,[],[f67,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  % (13094)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 0.21/0.53    inference(equality_resolution,[],[f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.53    inference(definition_unfolding,[],[f30,f48])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(X1,sK2) | ~r2_hidden(sK1,X1) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f93,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2))) )),
% 0.21/0.53    inference(equality_resolution,[],[f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 0.21/0.53    inference(equality_resolution,[],[f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.53    inference(definition_unfolding,[],[f32,f48])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X1] : (sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK1,X1) | ~r1_tarski(X1,sK2) | ~r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X1] : (sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK1,X1) | ~r1_tarski(X1,sK2) | ~r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) )),
% 0.21/0.53    inference(resolution,[],[f87,f85])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r1_tarski(X2,sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK1,X1) | ~r1_tarski(X1,sK2) | ~r2_hidden(sK0,X2) | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) )),
% 0.21/0.53    inference(resolution,[],[f84,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK0,sK2) | sK1 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK1,X0) | ~r1_tarski(X0,sK2)) )),
% 0.21/0.53    inference(resolution,[],[f82,f38])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(X1,sK2) | ~r2_hidden(sK1,X1) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f119,f64])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(sK1,X1) | ~r1_tarski(X1,sK2) | ~r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(sK1,X1) | ~r1_tarski(X1,sK2) | ~r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) )),
% 0.21/0.53    inference(resolution,[],[f113,f103])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r1_tarski(X2,sK2) | ~r2_hidden(sK1,X1) | ~r1_tarski(X1,sK2) | ~r2_hidden(sK0,X2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) )),
% 0.21/0.53    inference(resolution,[],[f111,f38])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK0,sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK1,X0) | ~r1_tarski(X0,sK2)) )),
% 0.21/0.53    inference(resolution,[],[f104,f38])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | sK0 = sK4(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.53    inference(resolution,[],[f103,f50])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(X1,sK2) | ~r2_hidden(sK1,X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f138,f64])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(X1,sK2) | ~r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,X1)) )),
% 0.21/0.53    inference(resolution,[],[f135,f130])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r1_tarski(X2,sK2) | ~r1_tarski(X1,sK2) | ~r2_hidden(sK0,X2) | ~r2_hidden(sK1,X1)) )),
% 0.21/0.53    inference(resolution,[],[f133,f38])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,X0) | ~r1_tarski(X0,sK2)) )),
% 0.21/0.53    inference(resolution,[],[f131,f38])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f50,f130])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (13070)------------------------------
% 0.21/0.53  % (13070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13070)Termination reason: Refutation
% 0.21/0.53  % (13081)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (13085)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  
% 0.21/0.53  % (13070)Memory used [KB]: 6268
% 0.21/0.53  % (13070)Time elapsed: 0.123 s
% 0.21/0.53  % (13070)------------------------------
% 0.21/0.53  % (13070)------------------------------
% 0.21/0.53  % (13096)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (13062)Success in time 0.175 s
%------------------------------------------------------------------------------
