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
% DateTime   : Thu Dec  3 12:35:31 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 147 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  349 ( 454 expanded)
%              Number of equality atoms :  284 ( 387 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f134,f154,f106])).

fof(f106,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X11,X9] :
      ( ~ sP0(X11,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | r2_hidden(X11,X9) ) ),
    inference(equality_resolution,[],[f72])).

% (30428)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f72,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X0 != X11
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
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

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f154,plain,(
    sP0(sK2,sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f115,f93])).

fof(f93,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f40,f90,f48,f90,f90])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f59,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK1 != sK2
    & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK1 != sK2
      & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f115,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
      | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) != X9 ) ),
    inference(definition_unfolding,[],[f83,f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f62,f48,f90])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ~ sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) )
      & ( sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) ) ),
    inference(definition_folding,[],[f25,f26])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

fof(f134,plain,(
    ~ r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f105])).

fof(f105,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f90])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

% (30440)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f41,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.17/0.52  % (30433)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.17/0.52  % (30441)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.17/0.52  % (30432)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.17/0.52  % (30423)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.17/0.52  % (30424)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.17/0.52  % (30449)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.53  % (30429)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.53  % (30441)Refutation not found, incomplete strategy% (30441)------------------------------
% 1.34/0.53  % (30441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (30434)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.53  % (30427)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.53  % (30446)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.53  % (30441)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (30441)Memory used [KB]: 1791
% 1.34/0.53  % (30441)Time elapsed: 0.116 s
% 1.34/0.53  % (30441)------------------------------
% 1.34/0.53  % (30441)------------------------------
% 1.34/0.53  % (30438)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.34/0.53  % (30449)Refutation not found, incomplete strategy% (30449)------------------------------
% 1.34/0.53  % (30449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (30449)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (30449)Memory used [KB]: 6268
% 1.34/0.53  % (30449)Time elapsed: 0.116 s
% 1.34/0.53  % (30449)------------------------------
% 1.34/0.53  % (30449)------------------------------
% 1.34/0.53  % (30451)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.53  % (30452)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.53  % (30452)Refutation not found, incomplete strategy% (30452)------------------------------
% 1.34/0.53  % (30452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (30452)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (30452)Memory used [KB]: 1663
% 1.34/0.53  % (30452)Time elapsed: 0.001 s
% 1.34/0.53  % (30452)------------------------------
% 1.34/0.53  % (30452)------------------------------
% 1.34/0.53  % (30425)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.34/0.54  % (30426)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.34/0.54  % (30434)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f176,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f134,f154,f106])).
% 1.34/0.54  fof(f106,plain,(
% 1.34/0.54    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X11,X9] : (~sP0(X11,X1,X2,X3,X4,X5,X6,X7,X8,X9) | r2_hidden(X11,X9)) )),
% 1.34/0.54    inference(equality_resolution,[],[f72])).
% 1.34/0.54  % (30428)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.54  fof(f72,plain,(
% 1.34/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X0 != X11 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f38])).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (((sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X0 != X11 & X1 != X11 & X2 != X11 & X3 != X11 & X4 != X11 & X5 != X11 & X6 != X11 & X7 != X11 & X8 != X11)) & (X0 = X11 | X1 = X11 | X2 = X11 | X3 = X11 | X4 = X11 | X5 = X11 | X6 = X11 | X7 = X11 | X8 = X11 | ~r2_hidden(X11,X9))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : (((X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10 & X8 != X10) | ~r2_hidden(X10,X9)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | X8 = X10 | r2_hidden(X10,X9))) => (((sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : (((X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10 & X8 != X10) | ~r2_hidden(X10,X9)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | X8 = X10 | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X0 != X11 & X1 != X11 & X2 != X11 & X3 != X11 & X4 != X11 & X5 != X11 & X6 != X11 & X7 != X11 & X8 != X11)) & (X0 = X11 | X1 = X11 | X2 = X11 | X3 = X11 | X4 = X11 | X5 = X11 | X6 = X11 | X7 = X11 | X8 = X11 | ~r2_hidden(X11,X9))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 1.34/0.54    inference(rectify,[],[f35])).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0,X9] : ((sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X9))) | ~sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)))),
% 1.34/0.54    inference(flattening,[],[f34])).
% 1.34/0.54  fof(f34,plain,(
% 1.34/0.54    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0,X9] : ((sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~r2_hidden(X10,X9))) | ~sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)))),
% 1.34/0.54    inference(nnf_transformation,[],[f26])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0,X9] : (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 1.34/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.34/0.54  fof(f154,plain,(
% 1.34/0.54    sP0(sK2,sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.34/0.54    inference(superposition,[],[f115,f93])).
% 1.34/0.54  fof(f93,plain,(
% 1.34/0.54    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.34/0.54    inference(definition_unfolding,[],[f40,f90,f48,f90,f90])).
% 1.34/0.54  fof(f48,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.34/0.54  fof(f90,plain,(
% 1.34/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f44,f89])).
% 1.34/0.54  fof(f89,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f47,f88])).
% 1.34/0.54  fof(f88,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f56,f87])).
% 1.34/0.54  fof(f87,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f58,f86])).
% 1.34/0.54  fof(f86,plain,(
% 1.34/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f59,f85])).
% 1.34/0.54  fof(f85,plain,(
% 1.34/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f60,f61])).
% 1.34/0.54  fof(f61,plain,(
% 1.34/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f19])).
% 1.34/0.54  fof(f19,axiom,(
% 1.34/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.34/0.54  fof(f60,plain,(
% 1.34/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f18])).
% 1.34/0.54  fof(f18,axiom,(
% 1.34/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.34/0.54  fof(f59,plain,(
% 1.34/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,axiom,(
% 1.34/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.34/0.54  fof(f58,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f16])).
% 1.34/0.54  fof(f16,axiom,(
% 1.34/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.34/0.54  fof(f56,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f15])).
% 1.34/0.54  fof(f15,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.54  fof(f47,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f14])).
% 1.34/0.54  fof(f14,axiom,(
% 1.34/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.54  fof(f44,plain,(
% 1.34/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f13])).
% 1.34/0.54  fof(f13,axiom,(
% 1.34/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.34/0.54    inference(cnf_transformation,[],[f29])).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    sK1 != sK2 & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK1 != sK2 & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.34/0.54    inference(ennf_transformation,[],[f21])).
% 1.34/0.54  fof(f21,negated_conjecture,(
% 1.34/0.54    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.34/0.54    inference(negated_conjecture,[],[f20])).
% 1.34/0.54  fof(f20,conjecture,(
% 1.34/0.54    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 1.34/0.54  fof(f115,plain,(
% 1.34/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) )),
% 1.34/0.54    inference(equality_resolution,[],[f102])).
% 1.34/0.54  fof(f102,plain,(
% 1.34/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) != X9) )),
% 1.34/0.54    inference(definition_unfolding,[],[f83,f91])).
% 1.34/0.54  fof(f91,plain,(
% 1.34/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) )),
% 1.34/0.54    inference(definition_unfolding,[],[f62,f48,f90])).
% 1.34/0.54  fof(f62,plain,(
% 1.34/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f12])).
% 1.34/0.54  fof(f12,axiom,(
% 1.34/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).
% 1.34/0.54  fof(f83,plain,(
% 1.34/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 1.34/0.54    inference(cnf_transformation,[],[f39])).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ~sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)) & (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 1.34/0.54    inference(nnf_transformation,[],[f27])).
% 1.34/0.54  fof(f27,plain,(
% 1.34/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9))),
% 1.34/0.54    inference(definition_folding,[],[f25,f26])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 1.34/0.54    inference(ennf_transformation,[],[f11])).
% 1.34/0.54  fof(f11,axiom,(
% 1.34/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).
% 1.34/0.54  fof(f134,plain,(
% 1.34/0.54    ~r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f41,f105])).
% 1.34/0.54  fof(f105,plain,(
% 1.34/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.34/0.54    inference(equality_resolution,[],[f100])).
% 1.34/0.54  fof(f100,plain,(
% 1.34/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.34/0.54    inference(definition_unfolding,[],[f52,f90])).
% 1.34/0.54  fof(f52,plain,(
% 1.34/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f33])).
% 1.34/0.54  % (30440)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.54    inference(rectify,[],[f30])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.54    inference(nnf_transformation,[],[f10])).
% 1.34/0.54  fof(f10,axiom,(
% 1.34/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.34/0.54  fof(f41,plain,(
% 1.34/0.54    sK1 != sK2),
% 1.34/0.54    inference(cnf_transformation,[],[f29])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (30434)------------------------------
% 1.34/0.54  % (30434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (30434)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (30434)Memory used [KB]: 6396
% 1.34/0.54  % (30434)Time elapsed: 0.128 s
% 1.34/0.54  % (30434)------------------------------
% 1.34/0.54  % (30434)------------------------------
% 1.34/0.54  % (30445)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.54  % (30422)Success in time 0.178 s
%------------------------------------------------------------------------------
