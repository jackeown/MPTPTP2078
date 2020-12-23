%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:31 EST 2020

% Result     : Theorem 4.15s
% Output     : Refutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  212 (3870837 expanded)
%              Number of leaves         :   22 (1328532 expanded)
%              Depth                    :   73
%              Number of atoms          :  502 (4098616 expanded)
%              Number of equality atoms :  435 (4098547 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal term depth       :   11 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4779,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4756,f151])).

fof(f151,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : ~ sP0(X0,sK2,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f128,f100])).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X11,X9] :
      ( ~ sP0(X0,X11,X2,X3,X4,X5,X6,X7,X8,X9)
      | r2_hidden(X11,X9) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X1 != X11
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ( ( ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
          & ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ( X0 != X11
                & X1 != X11
                & X2 != X11
                & X3 != X11
                & X4 != X11
                & X5 != X11
                & X6 != X11
                & X7 != X11
                & X8 != X11 ) )
            & ( X0 = X11
              | X1 = X11
              | X2 = X11
              | X3 = X11
              | X4 = X11
              | X5 = X11
              | X6 = X11
              | X7 = X11
              | X8 = X11
              | ~ r2_hidden(X11,X9) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X10] :
          ( ( ( X0 != X10
              & X1 != X10
              & X2 != X10
              & X3 != X10
              & X4 != X10
              & X5 != X10
              & X6 != X10
              & X7 != X10
              & X8 != X10 )
            | ~ r2_hidden(X10,X9) )
          & ( X0 = X10
            | X1 = X10
            | X2 = X10
            | X3 = X10
            | X4 = X10
            | X5 = X10
            | X6 = X10
            | X7 = X10
            | X8 = X10
            | r2_hidden(X10,X9) ) )
     => ( ( ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
        & ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ? [X10] :
            ( ( ( X0 != X10
                & X1 != X10
                & X2 != X10
                & X3 != X10
                & X4 != X10
                & X5 != X10
                & X6 != X10
                & X7 != X10
                & X8 != X10 )
              | ~ r2_hidden(X10,X9) )
            & ( X0 = X10
              | X1 = X10
              | X2 = X10
              | X3 = X10
              | X4 = X10
              | X5 = X10
              | X6 = X10
              | X7 = X10
              | X8 = X10
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ( X0 != X11
                & X1 != X11
                & X2 != X11
                & X3 != X11
                & X4 != X11
                & X5 != X11
                & X6 != X11
                & X7 != X11
                & X8 != X11 ) )
            & ( X0 = X11
              | X1 = X11
              | X2 = X11
              | X3 = X11
              | X4 = X11
              | X5 = X11
              | X6 = X11
              | X7 = X11
              | X8 = X11
              | ~ r2_hidden(X11,X9) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0,X9] :
      ( ( sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
        | ? [X10] :
            ( ( ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 )
              | ~ r2_hidden(X10,X9) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X9)
              | ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X9) ) )
        | ~ sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0,X9] :
      ( ( sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
        | ? [X10] :
            ( ( ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 )
              | ~ r2_hidden(X10,X9) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X9)
              | ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X9) ) )
        | ~ sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0,X9] :
      ( sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f128,plain,(
    ~ r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f98])).

fof(f98,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f85])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f37,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != sK2
    & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK1 != sK2
      & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f4756,plain,(
    sP0(sK1,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f195,f4755])).

fof(f4755,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(forward_demodulation,[],[f4754,f602])).

fof(f602,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f589,f38])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f589,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f564,f560])).

fof(f560,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f559,f558])).

fof(f558,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(forward_demodulation,[],[f552,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f552,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    inference(superposition,[],[f89,f200])).

fof(f200,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) ),
    inference(forward_demodulation,[],[f198,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f198,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0) ),
    inference(superposition,[],[f51,f191])).

fof(f191,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(forward_demodulation,[],[f190,f89])).

fof(f190,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(forward_demodulation,[],[f187,f38])).

fof(f187,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0)) ),
    inference(superposition,[],[f149,f88])).

fof(f88,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f41,f44,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f149,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) ),
    inference(forward_demodulation,[],[f148,f51])).

fof(f148,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) ),
    inference(superposition,[],[f51,f109])).

fof(f109,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f87,f40])).

fof(f87,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f36,f85,f79,f85,f85])).

fof(f36,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f42,f79])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f559,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) ),
    inference(forward_demodulation,[],[f553,f40])).

fof(f553,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) ),
    inference(superposition,[],[f88,f200])).

fof(f564,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) ),
    inference(superposition,[],[f51,f560])).

fof(f4754,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f4753,f3876])).

fof(f3876,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f51,f3825])).

fof(f3825,plain,(
    ! [X8] : k1_xboole_0 = k5_xboole_0(X8,X8) ),
    inference(forward_demodulation,[],[f3742,f3741])).

fof(f3741,plain,(
    ! [X6,X5] : k3_xboole_0(X6,k5_xboole_0(X6,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(X5,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X5)),X6)))))) = X6 ),
    inference(superposition,[],[f89,f3680])).

fof(f3680,plain,(
    ! [X19,X20] : k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X19)),X20) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(X19,X20))) ),
    inference(forward_demodulation,[],[f3679,f3251])).

fof(f3251,plain,(
    ! [X13] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X13)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X13))))) ),
    inference(forward_demodulation,[],[f3204,f2094])).

fof(f2094,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)))) ),
    inference(forward_demodulation,[],[f2093,f51])).

fof(f2093,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0))) ),
    inference(forward_demodulation,[],[f2083,f51])).

fof(f2083,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),X0)) ),
    inference(superposition,[],[f51,f2037])).

fof(f2037,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(forward_demodulation,[],[f2036,f199])).

fof(f199,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(forward_demodulation,[],[f197,f196])).

fof(f196,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(superposition,[],[f89,f191])).

fof(f197,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(superposition,[],[f88,f191])).

fof(f2036,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(forward_demodulation,[],[f2025,f361])).

fof(f361,plain,(
    ! [X4] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X4))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X4) ),
    inference(forward_demodulation,[],[f356,f237])).

fof(f237,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f222,f236])).

fof(f236,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) ),
    inference(superposition,[],[f51,f229])).

fof(f229,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(forward_demodulation,[],[f221,f38])).

fof(f221,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[],[f201,f199])).

fof(f201,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f51,f199])).

fof(f222,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f201,f201])).

fof(f356,plain,(
    ! [X4] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X4))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k1_xboole_0,X4)) ),
    inference(superposition,[],[f237,f323])).

fof(f323,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0))) ),
    inference(superposition,[],[f311,f274])).

fof(f274,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)))) ),
    inference(forward_demodulation,[],[f273,f51])).

fof(f273,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),X0))) ),
    inference(forward_demodulation,[],[f271,f51])).

fof(f271,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),X0)) ),
    inference(superposition,[],[f51,f265])).

fof(f265,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(superposition,[],[f264,f51])).

fof(f264,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f263,f260])).

fof(f260,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f259,f38])).

fof(f259,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f258,f38])).

fof(f258,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f256,f51])).

fof(f256,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f89,f251])).

fof(f251,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f89,f243])).

fof(f243,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f239,f201])).

fof(f239,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f201,f237])).

fof(f263,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f262,f38])).

fof(f262,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f261,f38])).

fof(f261,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0))))) ),
    inference(forward_demodulation,[],[f257,f51])).

fof(f257,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(superposition,[],[f88,f251])).

fof(f311,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X0))) ),
    inference(forward_demodulation,[],[f302,f243])).

fof(f302,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[],[f274,f274])).

fof(f2025,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(superposition,[],[f1585,f2019])).

fof(f2019,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(superposition,[],[f1993,f51])).

fof(f1993,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f1985,f229])).

fof(f1985,plain,(
    k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(superposition,[],[f1374,f1980])).

fof(f1980,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(forward_demodulation,[],[f1979,f89])).

fof(f1979,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(forward_demodulation,[],[f1978,f38])).

fof(f1978,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f1972,f51])).

fof(f1972,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0)) ),
    inference(superposition,[],[f1374,f88])).

fof(f1374,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) ),
    inference(forward_demodulation,[],[f1373,f51])).

fof(f1373,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) ),
    inference(superposition,[],[f51,f463])).

fof(f463,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f462,f459])).

fof(f459,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f458,f38])).

fof(f458,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f457,f38])).

fof(f457,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f455,f51])).

fof(f455,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f89,f451])).

fof(f451,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f448,f40])).

fof(f448,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0))) ),
    inference(superposition,[],[f89,f236])).

fof(f462,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(forward_demodulation,[],[f461,f38])).

fof(f461,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f460,f38])).

fof(f460,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k1_xboole_0))))) ),
    inference(forward_demodulation,[],[f456,f51])).

fof(f456,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(superposition,[],[f88,f451])).

fof(f1585,plain,(
    ! [X6] : k5_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X6)))) ),
    inference(forward_demodulation,[],[f1569,f1552])).

fof(f1552,plain,(
    ! [X12] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X12)))) = k5_xboole_0(k1_xboole_0,X12) ),
    inference(forward_demodulation,[],[f1551,f201])).

fof(f1551,plain,(
    ! [X12] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X12)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X12)) ),
    inference(forward_demodulation,[],[f1527,f313])).

fof(f313,plain,(
    ! [X2] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X2)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X2) ),
    inference(forward_demodulation,[],[f305,f237])).

fof(f305,plain,(
    ! [X2] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X2)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f237,f274])).

fof(f1527,plain,(
    ! [X12] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X12)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X12))))) ),
    inference(superposition,[],[f336,f1055])).

fof(f1055,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X2))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X2))) ),
    inference(superposition,[],[f311,f599])).

fof(f599,plain,(
    ! [X2] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X2)) ),
    inference(forward_demodulation,[],[f598,f236])).

fof(f598,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X2)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X2)) ),
    inference(forward_demodulation,[],[f587,f564])).

fof(f587,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X2)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X2))) ),
    inference(superposition,[],[f564,f200])).

fof(f336,plain,(
    ! [X4] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X4))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X4)) ),
    inference(forward_demodulation,[],[f329,f237])).

fof(f329,plain,(
    ! [X4] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X4))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X4))) ),
    inference(superposition,[],[f237,f311])).

fof(f1569,plain,(
    ! [X6] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X6)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X6)))) ),
    inference(superposition,[],[f1118,f1547])).

fof(f1547,plain,(
    ! [X9] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X9) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X9)))) ),
    inference(forward_demodulation,[],[f1546,f236])).

fof(f1546,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X9)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X9)) ),
    inference(forward_demodulation,[],[f1524,f274])).

fof(f1524,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X9)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X9))))) ),
    inference(superposition,[],[f311,f1055])).

fof(f1118,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0))))) ),
    inference(forward_demodulation,[],[f1117,f51])).

fof(f1117,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),X0)))) ),
    inference(forward_demodulation,[],[f1116,f51])).

fof(f1116,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),X0))) ),
    inference(forward_demodulation,[],[f1115,f51])).

fof(f1115,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))),X0)) ),
    inference(forward_demodulation,[],[f1112,f51])).

fof(f1112,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k1_xboole_0)),X0) ),
    inference(superposition,[],[f51,f896])).

fof(f896,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f877,f38])).

fof(f877,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)) ),
    inference(superposition,[],[f336,f265])).

fof(f3204,plain,(
    ! [X13] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X13))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X13))))) ),
    inference(superposition,[],[f2115,f2176])).

fof(f2176,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X2)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X2))) ),
    inference(forward_demodulation,[],[f2133,f2115])).

fof(f2133,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X2)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X2)))) ),
    inference(superposition,[],[f2115,f311])).

fof(f2115,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,X0))) ),
    inference(forward_demodulation,[],[f2099,f243])).

fof(f2099,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[],[f2094,f2094])).

fof(f3679,plain,(
    ! [X19,X20] : k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X19)),X20) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(X19,X20)))))) ),
    inference(forward_demodulation,[],[f3678,f51])).

fof(f3678,plain,(
    ! [X19,X20] : k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X19)),X20) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,X19),X20))))) ),
    inference(forward_demodulation,[],[f3677,f51])).

fof(f3677,plain,(
    ! [X19,X20] : k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X19)),X20) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X19)),X20)))) ),
    inference(forward_demodulation,[],[f3676,f51])).

fof(f3676,plain,(
    ! [X19,X20] : k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X19)),X20) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X19))),X20))) ),
    inference(forward_demodulation,[],[f3590,f51])).

fof(f3590,plain,(
    ! [X19,X20] : k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X19)),X20) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X19)))),X20)) ),
    inference(superposition,[],[f51,f3251])).

fof(f3742,plain,(
    ! [X8,X7] : k1_xboole_0 = k5_xboole_0(X8,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(X7,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X7)),X8))))))) ),
    inference(superposition,[],[f88,f3680])).

fof(f4753,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f4392,f38])).

fof(f4392,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k1_xboole_0) ),
    inference(superposition,[],[f956,f3875])).

fof(f3875,plain,(
    ! [X2,X3] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(superposition,[],[f3825,f51])).

fof(f956,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) ),
    inference(forward_demodulation,[],[f955,f236])).

fof(f955,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) ),
    inference(forward_demodulation,[],[f940,f613])).

fof(f613,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X1)) ),
    inference(backward_demodulation,[],[f586,f612])).

fof(f612,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) ),
    inference(superposition,[],[f51,f602])).

fof(f586,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f564,f564])).

fof(f940,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X0)))) ),
    inference(superposition,[],[f706,f201])).

fof(f706,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)))) ),
    inference(forward_demodulation,[],[f705,f51])).

fof(f705,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) ),
    inference(forward_demodulation,[],[f694,f51])).

fof(f694,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) ),
    inference(superposition,[],[f51,f533])).

fof(f533,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f532,f528])).

fof(f528,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f527,f229])).

fof(f527,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(forward_demodulation,[],[f526,f201])).

fof(f526,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(forward_demodulation,[],[f525,f51])).

fof(f525,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(forward_demodulation,[],[f523,f51])).

fof(f523,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(superposition,[],[f89,f196])).

fof(f532,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(forward_demodulation,[],[f531,f229])).

fof(f531,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(forward_demodulation,[],[f530,f201])).

fof(f530,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) ),
    inference(forward_demodulation,[],[f529,f51])).

fof(f529,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(forward_demodulation,[],[f524,f51])).

fof(f524,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(superposition,[],[f88,f196])).

fof(f195,plain,(
    sP0(sK1,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(superposition,[],[f108,f191])).

fof(f108,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
      | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) != X9 ) ),
    inference(definition_unfolding,[],[f77,f86])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(definition_unfolding,[],[f56,f79,f85])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ~ sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) )
      & ( sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) ) ),
    inference(definition_folding,[],[f21,f22])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (21086)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (21102)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (21094)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (21081)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (21083)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (21079)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (21080)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (21084)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (21078)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (21098)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (21091)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (21090)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (21088)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (21087)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (21089)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (21076)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (21104)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (21082)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (21096)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (21105)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (21103)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (21105)Refutation not found, incomplete strategy% (21105)------------------------------
% 0.20/0.54  % (21105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (21105)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (21105)Memory used [KB]: 1663
% 0.20/0.54  % (21105)Time elapsed: 0.001 s
% 0.20/0.54  % (21105)------------------------------
% 0.20/0.54  % (21105)------------------------------
% 0.20/0.54  % (21099)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.45/0.54  % (21097)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.45/0.54  % (21093)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.45/0.55  % (21085)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.45/0.55  % (21100)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.45/0.55  % (21095)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.45/0.55  % (21077)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.45/0.55  % (21101)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.45/0.55  % (21077)Refutation not found, incomplete strategy% (21077)------------------------------
% 1.45/0.55  % (21077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (21077)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (21077)Memory used [KB]: 1663
% 1.45/0.55  % (21077)Time elapsed: 0.136 s
% 1.45/0.55  % (21077)------------------------------
% 1.45/0.55  % (21077)------------------------------
% 1.45/0.55  % (21088)Refutation not found, incomplete strategy% (21088)------------------------------
% 1.45/0.55  % (21088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (21088)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (21088)Memory used [KB]: 10618
% 1.45/0.55  % (21088)Time elapsed: 0.152 s
% 1.45/0.55  % (21088)------------------------------
% 1.45/0.55  % (21088)------------------------------
% 1.45/0.56  % (21092)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.45/0.56  % (21092)Refutation not found, incomplete strategy% (21092)------------------------------
% 1.45/0.56  % (21092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (21092)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (21092)Memory used [KB]: 10746
% 1.60/0.57  % (21092)Time elapsed: 0.162 s
% 1.60/0.57  % (21092)------------------------------
% 1.60/0.57  % (21092)------------------------------
% 2.28/0.67  % (21079)Refutation not found, incomplete strategy% (21079)------------------------------
% 2.28/0.67  % (21079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.67  % (21079)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.67  
% 2.28/0.67  % (21079)Memory used [KB]: 6140
% 2.28/0.67  % (21079)Time elapsed: 0.247 s
% 2.28/0.67  % (21079)------------------------------
% 2.28/0.67  % (21079)------------------------------
% 2.28/0.68  % (21076)Refutation not found, incomplete strategy% (21076)------------------------------
% 2.28/0.68  % (21076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.68  % (21076)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.68  
% 2.28/0.68  % (21076)Memory used [KB]: 1663
% 2.28/0.68  % (21076)Time elapsed: 0.268 s
% 2.28/0.68  % (21076)------------------------------
% 2.28/0.68  % (21076)------------------------------
% 2.28/0.68  % (21107)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.28/0.68  % (21091)Refutation not found, incomplete strategy% (21091)------------------------------
% 2.28/0.68  % (21091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.68  % (21091)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.68  
% 2.28/0.68  % (21091)Memory used [KB]: 6140
% 2.28/0.68  % (21091)Time elapsed: 0.284 s
% 2.28/0.68  % (21091)------------------------------
% 2.28/0.68  % (21091)------------------------------
% 2.28/0.71  % (21109)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.28/0.71  % (21108)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.28/0.71  % (21108)Refutation not found, incomplete strategy% (21108)------------------------------
% 2.28/0.71  % (21108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.71  % (21108)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.71  
% 2.28/0.71  % (21108)Memory used [KB]: 6140
% 2.28/0.71  % (21108)Time elapsed: 0.129 s
% 2.28/0.71  % (21108)------------------------------
% 2.28/0.71  % (21108)------------------------------
% 2.74/0.73  % (21106)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.95/0.80  % (21110)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.95/0.81  % (21111)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.95/0.81  % (21112)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.95/0.82  % (21078)Time limit reached!
% 2.95/0.82  % (21078)------------------------------
% 2.95/0.82  % (21078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.82  % (21078)Termination reason: Time limit
% 2.95/0.82  % (21078)Termination phase: Saturation
% 2.95/0.82  
% 2.95/0.82  % (21078)Memory used [KB]: 6780
% 2.95/0.82  % (21078)Time elapsed: 0.400 s
% 2.95/0.82  % (21078)------------------------------
% 2.95/0.82  % (21078)------------------------------
% 2.95/0.82  % (21100)Time limit reached!
% 2.95/0.82  % (21100)------------------------------
% 2.95/0.82  % (21100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.82  % (21100)Termination reason: Time limit
% 2.95/0.82  
% 2.95/0.82  % (21100)Memory used [KB]: 14072
% 2.95/0.82  % (21100)Time elapsed: 0.421 s
% 2.95/0.82  % (21100)------------------------------
% 2.95/0.82  % (21100)------------------------------
% 3.37/0.84  % (21113)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.92/0.95  % (21082)Time limit reached!
% 3.92/0.95  % (21082)------------------------------
% 3.92/0.95  % (21082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.92/0.95  % (21082)Termination reason: Time limit
% 3.92/0.95  
% 3.92/0.95  % (21082)Memory used [KB]: 15735
% 3.92/0.95  % (21082)Time elapsed: 0.506 s
% 3.92/0.95  % (21082)------------------------------
% 3.92/0.95  % (21082)------------------------------
% 3.92/0.95  % (21090)Time limit reached!
% 3.92/0.95  % (21090)------------------------------
% 3.92/0.95  % (21090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.92/0.95  % (21115)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.92/0.95  % (21090)Termination reason: Time limit
% 3.92/0.95  
% 3.92/0.95  % (21090)Memory used [KB]: 6012
% 3.92/0.95  % (21090)Time elapsed: 0.515 s
% 3.92/0.95  % (21090)------------------------------
% 3.92/0.95  % (21090)------------------------------
% 4.15/0.97  % (21114)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 4.15/0.98  % (21087)Refutation found. Thanks to Tanya!
% 4.15/0.98  % SZS status Theorem for theBenchmark
% 4.15/0.98  % SZS output start Proof for theBenchmark
% 4.15/0.98  fof(f4779,plain,(
% 4.15/0.98    $false),
% 4.15/0.98    inference(subsumption_resolution,[],[f4756,f151])).
% 4.15/0.98  fof(f151,plain,(
% 4.15/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~sP0(X0,sK2,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 4.15/0.98    inference(unit_resulting_resolution,[],[f128,f100])).
% 4.15/0.98  fof(f100,plain,(
% 4.15/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X11,X9] : (~sP0(X0,X11,X2,X3,X4,X5,X6,X7,X8,X9) | r2_hidden(X11,X9)) )),
% 4.15/0.98    inference(equality_resolution,[],[f65])).
% 4.15/0.98  fof(f65,plain,(
% 4.15/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X1 != X11 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 4.15/0.98    inference(cnf_transformation,[],[f34])).
% 4.15/0.98  fof(f34,plain,(
% 4.15/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (((sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X0 != X11 & X1 != X11 & X2 != X11 & X3 != X11 & X4 != X11 & X5 != X11 & X6 != X11 & X7 != X11 & X8 != X11)) & (X0 = X11 | X1 = X11 | X2 = X11 | X3 = X11 | X4 = X11 | X5 = X11 | X6 = X11 | X7 = X11 | X8 = X11 | ~r2_hidden(X11,X9))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 4.15/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 4.15/0.98  fof(f33,plain,(
% 4.15/0.98    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : (((X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10 & X8 != X10) | ~r2_hidden(X10,X9)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | X8 = X10 | r2_hidden(X10,X9))) => (((sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 4.15/0.98    introduced(choice_axiom,[])).
% 4.15/0.98  fof(f32,plain,(
% 4.15/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : (((X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10 & X8 != X10) | ~r2_hidden(X10,X9)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | X8 = X10 | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X0 != X11 & X1 != X11 & X2 != X11 & X3 != X11 & X4 != X11 & X5 != X11 & X6 != X11 & X7 != X11 & X8 != X11)) & (X0 = X11 | X1 = X11 | X2 = X11 | X3 = X11 | X4 = X11 | X5 = X11 | X6 = X11 | X7 = X11 | X8 = X11 | ~r2_hidden(X11,X9))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 4.15/0.98    inference(rectify,[],[f31])).
% 4.15/0.98  fof(f31,plain,(
% 4.15/0.98    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0,X9] : ((sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X9))) | ~sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)))),
% 4.15/0.98    inference(flattening,[],[f30])).
% 4.15/0.98  fof(f30,plain,(
% 4.15/0.98    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0,X9] : ((sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~r2_hidden(X10,X9))) | ~sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)))),
% 4.15/0.98    inference(nnf_transformation,[],[f22])).
% 4.15/0.98  fof(f22,plain,(
% 4.15/0.98    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0,X9] : (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 4.15/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.15/0.98  fof(f128,plain,(
% 4.15/0.98    ~r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 4.15/0.98    inference(unit_resulting_resolution,[],[f37,f98])).
% 4.15/0.98  fof(f98,plain,(
% 4.15/0.98    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 4.15/0.98    inference(equality_resolution,[],[f93])).
% 4.15/0.98  fof(f93,plain,(
% 4.15/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 4.15/0.98    inference(definition_unfolding,[],[f46,f85])).
% 4.15/0.98  fof(f85,plain,(
% 4.15/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.15/0.98    inference(definition_unfolding,[],[f39,f84])).
% 4.15/0.98  fof(f84,plain,(
% 4.15/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.15/0.98    inference(definition_unfolding,[],[f43,f83])).
% 4.15/0.98  fof(f83,plain,(
% 4.15/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.15/0.98    inference(definition_unfolding,[],[f50,f82])).
% 4.15/0.98  fof(f82,plain,(
% 4.15/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.15/0.98    inference(definition_unfolding,[],[f52,f81])).
% 4.15/0.98  fof(f81,plain,(
% 4.15/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.15/0.98    inference(definition_unfolding,[],[f53,f80])).
% 4.15/0.98  fof(f80,plain,(
% 4.15/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.15/0.98    inference(definition_unfolding,[],[f54,f55])).
% 4.15/0.98  fof(f55,plain,(
% 4.15/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.15/0.98    inference(cnf_transformation,[],[f17])).
% 4.15/0.98  fof(f17,axiom,(
% 4.15/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 4.15/0.98  fof(f54,plain,(
% 4.15/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 4.15/0.98    inference(cnf_transformation,[],[f16])).
% 4.15/0.98  fof(f16,axiom,(
% 4.15/0.98    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 4.15/0.98  fof(f53,plain,(
% 4.15/0.98    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.15/0.98    inference(cnf_transformation,[],[f15])).
% 4.15/0.98  fof(f15,axiom,(
% 4.15/0.98    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 4.15/0.98  fof(f52,plain,(
% 4.15/0.98    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 4.15/0.98    inference(cnf_transformation,[],[f14])).
% 4.15/0.98  fof(f14,axiom,(
% 4.15/0.98    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 4.15/0.98  fof(f50,plain,(
% 4.15/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.15/0.98    inference(cnf_transformation,[],[f13])).
% 4.15/0.98  fof(f13,axiom,(
% 4.15/0.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 4.15/0.98  fof(f43,plain,(
% 4.15/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.15/0.98    inference(cnf_transformation,[],[f12])).
% 4.15/0.98  fof(f12,axiom,(
% 4.15/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 4.15/0.98  fof(f39,plain,(
% 4.15/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.15/0.98    inference(cnf_transformation,[],[f11])).
% 4.15/0.98  fof(f11,axiom,(
% 4.15/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 4.15/0.98  fof(f46,plain,(
% 4.15/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 4.15/0.98    inference(cnf_transformation,[],[f29])).
% 4.15/0.98  fof(f29,plain,(
% 4.15/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.15/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 4.15/0.98  fof(f28,plain,(
% 4.15/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 4.15/0.98    introduced(choice_axiom,[])).
% 4.15/0.98  fof(f27,plain,(
% 4.15/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.15/0.98    inference(rectify,[],[f26])).
% 4.15/0.98  fof(f26,plain,(
% 4.15/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 4.15/0.98    inference(nnf_transformation,[],[f8])).
% 4.15/0.98  fof(f8,axiom,(
% 4.15/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 4.15/0.98  fof(f37,plain,(
% 4.15/0.98    sK1 != sK2),
% 4.15/0.98    inference(cnf_transformation,[],[f25])).
% 4.15/0.98  fof(f25,plain,(
% 4.15/0.98    sK1 != sK2 & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 4.15/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f24])).
% 4.15/0.98  fof(f24,plain,(
% 4.15/0.98    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK1 != sK2 & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 4.15/0.98    introduced(choice_axiom,[])).
% 4.15/0.98  fof(f20,plain,(
% 4.15/0.98    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 4.15/0.98    inference(ennf_transformation,[],[f19])).
% 4.15/0.98  fof(f19,negated_conjecture,(
% 4.15/0.98    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 4.15/0.98    inference(negated_conjecture,[],[f18])).
% 4.15/0.98  fof(f18,conjecture,(
% 4.15/0.98    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 4.15/0.98  fof(f4756,plain,(
% 4.15/0.98    sP0(sK1,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 4.15/0.98    inference(backward_demodulation,[],[f195,f4755])).
% 4.15/0.98  fof(f4755,plain,(
% 4.15/0.98    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),
% 4.15/0.98    inference(forward_demodulation,[],[f4754,f602])).
% 4.15/0.98  fof(f602,plain,(
% 4.15/0.98    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 4.15/0.98    inference(forward_demodulation,[],[f589,f38])).
% 4.15/0.98  fof(f38,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.15/0.98    inference(cnf_transformation,[],[f5])).
% 4.15/0.98  fof(f5,axiom,(
% 4.15/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 4.15/0.98  fof(f589,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 4.15/0.98    inference(superposition,[],[f564,f560])).
% 4.15/0.98  fof(f560,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 4.15/0.98    inference(forward_demodulation,[],[f559,f558])).
% 4.15/0.98  fof(f558,plain,(
% 4.15/0.98    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 4.15/0.98    inference(forward_demodulation,[],[f552,f40])).
% 4.15/0.98  fof(f40,plain,(
% 4.15/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.15/0.98    inference(cnf_transformation,[],[f1])).
% 4.15/0.98  fof(f1,axiom,(
% 4.15/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.15/0.98  fof(f552,plain,(
% 4.15/0.98    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))),
% 4.15/0.98    inference(superposition,[],[f89,f200])).
% 4.15/0.98  fof(f200,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f198,f51])).
% 4.15/0.98  fof(f51,plain,(
% 4.15/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.15/0.98    inference(cnf_transformation,[],[f6])).
% 4.15/0.98  fof(f6,axiom,(
% 4.15/0.98    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.15/0.98  fof(f198,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) )),
% 4.15/0.98    inference(superposition,[],[f51,f191])).
% 4.15/0.98  fof(f191,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),
% 4.15/0.98    inference(forward_demodulation,[],[f190,f89])).
% 4.15/0.98  fof(f190,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f187,f38])).
% 4.15/0.98  fof(f187,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0))) )),
% 4.15/0.98    inference(superposition,[],[f149,f88])).
% 4.15/0.98  fof(f88,plain,(
% 4.15/0.98    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 4.15/0.98    inference(definition_unfolding,[],[f41,f44,f79])).
% 4.15/0.98  fof(f79,plain,(
% 4.15/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 4.15/0.98    inference(definition_unfolding,[],[f45,f44])).
% 4.15/0.98  fof(f45,plain,(
% 4.15/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.15/0.98    inference(cnf_transformation,[],[f7])).
% 4.15/0.98  fof(f7,axiom,(
% 4.15/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 4.15/0.98  fof(f44,plain,(
% 4.15/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.15/0.98    inference(cnf_transformation,[],[f2])).
% 4.15/0.98  fof(f2,axiom,(
% 4.15/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.15/0.98  fof(f41,plain,(
% 4.15/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 4.15/0.98    inference(cnf_transformation,[],[f4])).
% 4.15/0.98  fof(f4,axiom,(
% 4.15/0.98    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 4.15/0.98  fof(f149,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f148,f51])).
% 4.15/0.98  fof(f148,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) )),
% 4.15/0.98    inference(superposition,[],[f51,f109])).
% 4.15/0.98  fof(f109,plain,(
% 4.15/0.98    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 4.15/0.98    inference(forward_demodulation,[],[f87,f40])).
% 4.15/0.98  fof(f87,plain,(
% 4.15/0.98    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 4.15/0.98    inference(definition_unfolding,[],[f36,f85,f79,f85,f85])).
% 4.15/0.98  fof(f36,plain,(
% 4.15/0.98    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 4.15/0.98    inference(cnf_transformation,[],[f25])).
% 4.15/0.98  fof(f89,plain,(
% 4.15/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 4.15/0.98    inference(definition_unfolding,[],[f42,f79])).
% 4.15/0.98  fof(f42,plain,(
% 4.15/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 4.15/0.98    inference(cnf_transformation,[],[f3])).
% 4.15/0.98  fof(f3,axiom,(
% 4.15/0.98    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 4.15/0.98  fof(f559,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))))),
% 4.15/0.98    inference(forward_demodulation,[],[f553,f40])).
% 4.15/0.98  fof(f553,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))),
% 4.15/0.98    inference(superposition,[],[f88,f200])).
% 4.15/0.98  fof(f564,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) )),
% 4.15/0.98    inference(superposition,[],[f51,f560])).
% 4.15/0.98  fof(f4754,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 4.15/0.98    inference(forward_demodulation,[],[f4753,f3876])).
% 4.15/0.98  fof(f3876,plain,(
% 4.15/0.98    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 4.15/0.98    inference(superposition,[],[f51,f3825])).
% 4.15/0.98  fof(f3825,plain,(
% 4.15/0.98    ( ! [X8] : (k1_xboole_0 = k5_xboole_0(X8,X8)) )),
% 4.15/0.98    inference(forward_demodulation,[],[f3742,f3741])).
% 4.15/0.98  fof(f3741,plain,(
% 4.15/0.98    ( ! [X6,X5] : (k3_xboole_0(X6,k5_xboole_0(X6,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(X5,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X5)),X6)))))) = X6) )),
% 4.15/0.98    inference(superposition,[],[f89,f3680])).
% 4.15/0.98  fof(f3680,plain,(
% 4.15/0.98    ( ! [X19,X20] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X19)),X20) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(X19,X20)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f3679,f3251])).
% 4.15/0.98  fof(f3251,plain,(
% 4.15/0.98    ( ! [X13] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X13)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X13)))))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f3204,f2094])).
% 4.15/0.98  fof(f2094,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f2093,f51])).
% 4.15/0.98  fof(f2093,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f2083,f51])).
% 4.15/0.98  fof(f2083,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),X0))) )),
% 4.15/0.98    inference(superposition,[],[f51,f2037])).
% 4.15/0.98  fof(f2037,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 4.15/0.98    inference(forward_demodulation,[],[f2036,f199])).
% 4.15/0.98  fof(f199,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 4.15/0.98    inference(forward_demodulation,[],[f197,f196])).
% 4.15/0.98  fof(f196,plain,(
% 4.15/0.98    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 4.15/0.98    inference(superposition,[],[f89,f191])).
% 4.15/0.98  fof(f197,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 4.15/0.98    inference(superposition,[],[f88,f191])).
% 4.15/0.98  fof(f2036,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 4.15/0.98    inference(forward_demodulation,[],[f2025,f361])).
% 4.15/0.98  fof(f361,plain,(
% 4.15/0.98    ( ! [X4] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X4))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X4)) )),
% 4.15/0.98    inference(forward_demodulation,[],[f356,f237])).
% 4.15/0.98  fof(f237,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k1_xboole_0,X0))) )),
% 4.15/0.98    inference(backward_demodulation,[],[f222,f236])).
% 4.15/0.98  fof(f236,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0))) )),
% 4.15/0.98    inference(superposition,[],[f51,f229])).
% 4.15/0.98  fof(f229,plain,(
% 4.15/0.98    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 4.15/0.98    inference(forward_demodulation,[],[f221,f38])).
% 4.15/0.98  fof(f221,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 4.15/0.98    inference(superposition,[],[f201,f199])).
% 4.15/0.98  fof(f201,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 4.15/0.98    inference(superposition,[],[f51,f199])).
% 4.15/0.98  fof(f222,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k1_xboole_0,X0))) )),
% 4.15/0.98    inference(superposition,[],[f201,f201])).
% 4.15/0.98  fof(f356,plain,(
% 4.15/0.98    ( ! [X4] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X4))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k1_xboole_0,X4))) )),
% 4.15/0.98    inference(superposition,[],[f237,f323])).
% 4.15/0.98  fof(f323,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)))) )),
% 4.15/0.98    inference(superposition,[],[f311,f274])).
% 4.15/0.98  fof(f274,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0))))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f273,f51])).
% 4.15/0.98  fof(f273,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),X0)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f271,f51])).
% 4.15/0.98  fof(f271,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),X0))) )),
% 4.15/0.98    inference(superposition,[],[f51,f265])).
% 4.15/0.98  fof(f265,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))))),
% 4.15/0.98    inference(superposition,[],[f264,f51])).
% 4.15/0.98  fof(f264,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))),
% 4.15/0.98    inference(forward_demodulation,[],[f263,f260])).
% 4.15/0.98  fof(f260,plain,(
% 4.15/0.98    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))),
% 4.15/0.98    inference(forward_demodulation,[],[f259,f38])).
% 4.15/0.98  fof(f259,plain,(
% 4.15/0.98    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)))),
% 4.15/0.98    inference(forward_demodulation,[],[f258,f38])).
% 4.15/0.98  fof(f258,plain,(
% 4.15/0.98    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0))))),
% 4.15/0.98    inference(forward_demodulation,[],[f256,f51])).
% 4.15/0.98  fof(f256,plain,(
% 4.15/0.98    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_xboole_0)))),
% 4.15/0.98    inference(superposition,[],[f89,f251])).
% 4.15/0.98  fof(f251,plain,(
% 4.15/0.98    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))),
% 4.15/0.98    inference(superposition,[],[f89,f243])).
% 4.15/0.98  fof(f243,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f239,f201])).
% 4.15/0.98  fof(f239,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 4.15/0.98    inference(superposition,[],[f201,f237])).
% 4.15/0.98  fof(f263,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))))),
% 4.15/0.98    inference(forward_demodulation,[],[f262,f38])).
% 4.15/0.98  fof(f262,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0))))),
% 4.15/0.98    inference(forward_demodulation,[],[f261,f38])).
% 4.15/0.98  fof(f261,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0)))))),
% 4.15/0.98    inference(forward_demodulation,[],[f257,f51])).
% 4.15/0.98  fof(f257,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_xboole_0))))),
% 4.15/0.98    inference(superposition,[],[f88,f251])).
% 4.15/0.98  fof(f311,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X0)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f302,f243])).
% 4.15/0.98  fof(f302,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X0)))) )),
% 4.15/0.98    inference(superposition,[],[f274,f274])).
% 4.15/0.98  fof(f2025,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 4.15/0.98    inference(superposition,[],[f1585,f2019])).
% 4.15/0.98  fof(f2019,plain,(
% 4.15/0.98    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 4.15/0.98    inference(superposition,[],[f1993,f51])).
% 4.15/0.98  fof(f1993,plain,(
% 4.15/0.98    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 4.15/0.98    inference(forward_demodulation,[],[f1985,f229])).
% 4.15/0.98  fof(f1985,plain,(
% 4.15/0.98    k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 4.15/0.98    inference(superposition,[],[f1374,f1980])).
% 4.15/0.98  fof(f1980,plain,(
% 4.15/0.98    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),
% 4.15/0.98    inference(forward_demodulation,[],[f1979,f89])).
% 4.15/0.98  fof(f1979,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f1978,f38])).
% 4.15/0.98  fof(f1978,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f1972,f51])).
% 4.15/0.98  fof(f1972,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0))) )),
% 4.15/0.98    inference(superposition,[],[f1374,f88])).
% 4.15/0.98  fof(f1374,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f1373,f51])).
% 4.15/0.98  fof(f1373,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0))) )),
% 4.15/0.98    inference(superposition,[],[f51,f463])).
% 4.15/0.98  fof(f463,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 4.15/0.98    inference(forward_demodulation,[],[f462,f459])).
% 4.15/0.98  fof(f459,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 4.15/0.98    inference(forward_demodulation,[],[f458,f38])).
% 4.15/0.98  fof(f458,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_xboole_0)))),
% 4.15/0.98    inference(forward_demodulation,[],[f457,f38])).
% 4.15/0.98  fof(f457,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k1_xboole_0))))),
% 4.15/0.98    inference(forward_demodulation,[],[f455,f51])).
% 4.15/0.98  fof(f455,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k1_xboole_0,k1_xboole_0)))),
% 4.15/0.98    inference(superposition,[],[f89,f451])).
% 4.15/0.98  fof(f451,plain,(
% 4.15/0.98    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 4.15/0.98    inference(forward_demodulation,[],[f448,f40])).
% 4.15/0.98  fof(f448,plain,(
% 4.15/0.98    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0)))),
% 4.15/0.98    inference(superposition,[],[f89,f236])).
% 4.15/0.98  fof(f462,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 4.15/0.98    inference(forward_demodulation,[],[f461,f38])).
% 4.15/0.98  fof(f461,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_xboole_0))))),
% 4.15/0.98    inference(forward_demodulation,[],[f460,f38])).
% 4.15/0.98  fof(f460,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k1_xboole_0)))))),
% 4.15/0.98    inference(forward_demodulation,[],[f456,f51])).
% 4.15/0.98  fof(f456,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k1_xboole_0,k1_xboole_0))))),
% 4.15/0.98    inference(superposition,[],[f88,f451])).
% 4.15/0.98  fof(f1585,plain,(
% 4.15/0.98    ( ! [X6] : (k5_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X6))))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f1569,f1552])).
% 4.15/0.98  fof(f1552,plain,(
% 4.15/0.98    ( ! [X12] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X12)))) = k5_xboole_0(k1_xboole_0,X12)) )),
% 4.15/0.98    inference(forward_demodulation,[],[f1551,f201])).
% 4.15/0.98  fof(f1551,plain,(
% 4.15/0.98    ( ! [X12] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X12)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X12))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f1527,f313])).
% 4.15/0.98  fof(f313,plain,(
% 4.15/0.98    ( ! [X2] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X2)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X2)) )),
% 4.15/0.98    inference(forward_demodulation,[],[f305,f237])).
% 4.15/0.98  fof(f305,plain,(
% 4.15/0.98    ( ! [X2] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X2)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k1_xboole_0,X2))) )),
% 4.15/0.98    inference(superposition,[],[f237,f274])).
% 4.15/0.98  fof(f1527,plain,(
% 4.15/0.98    ( ! [X12] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X12)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X12)))))) )),
% 4.15/0.98    inference(superposition,[],[f336,f1055])).
% 4.15/0.98  fof(f1055,plain,(
% 4.15/0.98    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X2))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X2)))) )),
% 4.15/0.98    inference(superposition,[],[f311,f599])).
% 4.15/0.98  fof(f599,plain,(
% 4.15/0.98    ( ! [X2] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X2))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f598,f236])).
% 4.15/0.98  fof(f598,plain,(
% 4.15/0.98    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X2)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X2))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f587,f564])).
% 4.15/0.98  fof(f587,plain,(
% 4.15/0.98    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X2)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X2)))) )),
% 4.15/0.98    inference(superposition,[],[f564,f200])).
% 4.15/0.98  fof(f336,plain,(
% 4.15/0.98    ( ! [X4] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X4))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X4))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f329,f237])).
% 4.15/0.98  fof(f329,plain,(
% 4.15/0.98    ( ! [X4] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X4))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X4)))) )),
% 4.15/0.98    inference(superposition,[],[f237,f311])).
% 4.15/0.98  fof(f1569,plain,(
% 4.15/0.98    ( ! [X6] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X6)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X6))))) )),
% 4.15/0.98    inference(superposition,[],[f1118,f1547])).
% 4.15/0.98  fof(f1547,plain,(
% 4.15/0.98    ( ! [X9] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X9) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X9))))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f1546,f236])).
% 4.15/0.98  fof(f1546,plain,(
% 4.15/0.98    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X9)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X9))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f1524,f274])).
% 4.15/0.98  fof(f1524,plain,(
% 4.15/0.98    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X9)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X9)))))) )),
% 4.15/0.98    inference(superposition,[],[f311,f1055])).
% 4.15/0.98  fof(f1118,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)))))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f1117,f51])).
% 4.15/0.98  fof(f1117,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),X0))))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f1116,f51])).
% 4.15/0.98  fof(f1116,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),X0)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f1115,f51])).
% 4.15/0.98  fof(f1115,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))),X0))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f1112,f51])).
% 4.15/0.98  fof(f1112,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k1_xboole_0)),X0)) )),
% 4.15/0.98    inference(superposition,[],[f51,f896])).
% 4.15/0.98  fof(f896,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k1_xboole_0))),
% 4.15/0.98    inference(forward_demodulation,[],[f877,f38])).
% 4.15/0.98  fof(f877,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0))),
% 4.15/0.98    inference(superposition,[],[f336,f265])).
% 4.15/0.98  fof(f3204,plain,(
% 4.15/0.98    ( ! [X13] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X13))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X13)))))) )),
% 4.15/0.98    inference(superposition,[],[f2115,f2176])).
% 4.15/0.98  fof(f2176,plain,(
% 4.15/0.98    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X2)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X2)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f2133,f2115])).
% 4.15/0.98  fof(f2133,plain,(
% 4.15/0.98    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X2)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X2))))) )),
% 4.15/0.98    inference(superposition,[],[f2115,f311])).
% 4.15/0.98  fof(f2115,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,X0)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f2099,f243])).
% 4.15/0.98  fof(f2099,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k1_xboole_0,X0)))) )),
% 4.15/0.98    inference(superposition,[],[f2094,f2094])).
% 4.15/0.98  fof(f3679,plain,(
% 4.15/0.98    ( ! [X19,X20] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X19)),X20) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(X19,X20))))))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f3678,f51])).
% 4.15/0.98  fof(f3678,plain,(
% 4.15/0.98    ( ! [X19,X20] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X19)),X20) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,X19),X20)))))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f3677,f51])).
% 4.15/0.98  fof(f3677,plain,(
% 4.15/0.98    ( ! [X19,X20] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X19)),X20) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X19)),X20))))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f3676,f51])).
% 4.15/0.98  fof(f3676,plain,(
% 4.15/0.98    ( ! [X19,X20] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X19)),X20) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X19))),X20)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f3590,f51])).
% 4.15/0.98  fof(f3590,plain,(
% 4.15/0.98    ( ! [X19,X20] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X19)),X20) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,X19)))),X20))) )),
% 4.15/0.98    inference(superposition,[],[f51,f3251])).
% 4.15/0.98  fof(f3742,plain,(
% 4.15/0.98    ( ! [X8,X7] : (k1_xboole_0 = k5_xboole_0(X8,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(X7,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X7)),X8)))))))) )),
% 4.15/0.98    inference(superposition,[],[f88,f3680])).
% 4.15/0.98  fof(f4753,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 4.15/0.98    inference(forward_demodulation,[],[f4392,f38])).
% 4.15/0.98  fof(f4392,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k1_xboole_0)),
% 4.15/0.98    inference(superposition,[],[f956,f3875])).
% 4.15/0.98  fof(f3875,plain,(
% 4.15/0.98    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 4.15/0.98    inference(superposition,[],[f3825,f51])).
% 4.15/0.98  fof(f956,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f955,f236])).
% 4.15/0.98  fof(f955,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f940,f613])).
% 4.15/0.98  fof(f613,plain,(
% 4.15/0.98    ( ! [X1] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X1))) )),
% 4.15/0.98    inference(backward_demodulation,[],[f586,f612])).
% 4.15/0.98  fof(f612,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) )),
% 4.15/0.98    inference(superposition,[],[f51,f602])).
% 4.15/0.98  fof(f586,plain,(
% 4.15/0.98    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X1))) )),
% 4.15/0.98    inference(superposition,[],[f564,f564])).
% 4.15/0.98  fof(f940,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X0))))) )),
% 4.15/0.98    inference(superposition,[],[f706,f201])).
% 4.15/0.98  fof(f706,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0))))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f705,f51])).
% 4.15/0.98  fof(f705,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)))) )),
% 4.15/0.98    inference(forward_demodulation,[],[f694,f51])).
% 4.15/0.98  fof(f694,plain,(
% 4.15/0.98    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0))) )),
% 4.15/0.98    inference(superposition,[],[f51,f533])).
% 4.15/0.98  fof(f533,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 4.15/0.98    inference(forward_demodulation,[],[f532,f528])).
% 4.15/0.98  fof(f528,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 4.15/0.98    inference(forward_demodulation,[],[f527,f229])).
% 4.15/0.98  fof(f527,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 4.15/0.98    inference(forward_demodulation,[],[f526,f201])).
% 4.15/0.98  fof(f526,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 4.15/0.98    inference(forward_demodulation,[],[f525,f51])).
% 4.15/0.98  fof(f525,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 4.15/0.98    inference(forward_demodulation,[],[f523,f51])).
% 4.15/0.98  fof(f523,plain,(
% 4.15/0.98    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 4.15/0.98    inference(superposition,[],[f89,f196])).
% 4.15/0.98  fof(f532,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 4.15/0.98    inference(forward_demodulation,[],[f531,f229])).
% 4.15/0.98  fof(f531,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 4.15/0.98    inference(forward_demodulation,[],[f530,f201])).
% 4.15/0.98  fof(f530,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))))),
% 4.15/0.98    inference(forward_demodulation,[],[f529,f51])).
% 4.15/0.98  fof(f529,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 4.15/0.98    inference(forward_demodulation,[],[f524,f51])).
% 4.15/0.98  fof(f524,plain,(
% 4.15/0.98    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 4.15/0.98    inference(superposition,[],[f88,f196])).
% 4.15/0.98  fof(f195,plain,(
% 4.15/0.98    sP0(sK1,sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 4.15/0.98    inference(superposition,[],[f108,f191])).
% 4.15/0.98  fof(f108,plain,(
% 4.15/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))))) )),
% 4.15/0.98    inference(equality_resolution,[],[f95])).
% 4.15/0.98  fof(f95,plain,(
% 4.15/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) != X9) )),
% 4.15/0.98    inference(definition_unfolding,[],[f77,f86])).
% 4.15/0.98  fof(f86,plain,(
% 4.15/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) )),
% 4.15/0.98    inference(definition_unfolding,[],[f56,f79,f85])).
% 4.15/0.98  fof(f56,plain,(
% 4.15/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))) )),
% 4.15/0.98    inference(cnf_transformation,[],[f10])).
% 4.15/0.98  fof(f10,axiom,(
% 4.15/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).
% 4.15/0.98  fof(f77,plain,(
% 4.15/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 4.15/0.98    inference(cnf_transformation,[],[f35])).
% 4.15/0.98  fof(f35,plain,(
% 4.15/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ~sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)) & (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 4.15/0.98    inference(nnf_transformation,[],[f23])).
% 4.15/0.98  fof(f23,plain,(
% 4.15/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9))),
% 4.15/0.98    inference(definition_folding,[],[f21,f22])).
% 4.15/0.98  fof(f21,plain,(
% 4.15/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 4.15/0.98    inference(ennf_transformation,[],[f9])).
% 4.15/0.98  fof(f9,axiom,(
% 4.15/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 4.15/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).
% 4.15/0.98  % SZS output end Proof for theBenchmark
% 4.15/0.98  % (21087)------------------------------
% 4.15/0.98  % (21087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/0.98  % (21087)Termination reason: Refutation
% 4.15/0.98  
% 4.15/0.98  % (21087)Memory used [KB]: 10490
% 4.15/0.98  % (21087)Time elapsed: 0.537 s
% 4.15/0.98  % (21087)------------------------------
% 4.15/0.98  % (21087)------------------------------
% 4.15/0.98  % (21075)Success in time 0.613 s
%------------------------------------------------------------------------------
