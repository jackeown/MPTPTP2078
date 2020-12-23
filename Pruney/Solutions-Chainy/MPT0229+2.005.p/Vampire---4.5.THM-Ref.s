%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:30 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 144 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  261 ( 346 expanded)
%              Number of equality atoms :  162 ( 237 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f43,f99,f282])).

fof(f282,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK2,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
      | sK3 = X0 ) ),
    inference(resolution,[],[f273,f98])).

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
    inference(definition_unfolding,[],[f53,f86])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f273,plain,(
    ! [X0] :
      ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
      | ~ sP0(X0,sK2,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ) ),
    inference(resolution,[],[f271,f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X11,X9) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ( ( ~ sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
          & ( sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X10] :
          ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X10,X9) )
          & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X10,X9) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
        & ( sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ? [X10] :
            ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X9) )
            & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ? [X10] :
            ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X9) )
            & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X9)
              | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(nnf_transformation,[],[f26])).

% (14046)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f271,plain,(
    sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(forward_demodulation,[],[f270,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f270,plain,(
    sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f260,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f260,plain,(
    sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(superposition,[],[f108,f110])).

fof(f110,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f88,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f88,plain,(
    r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f42,f86,f86])).

fof(f42,plain,(
    r1_tarski(k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK2 != sK3
    & r1_tarski(k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK2 != sK3
      & r1_tarski(k1_tarski(sK2),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(f108,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) != X9 ) ),
    inference(definition_unfolding,[],[f78,f87])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(definition_unfolding,[],[f63,f80,f86])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(definition_folding,[],[f24,f26,f25])).

fof(f25,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

fof(f99,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8
          & X0 != X9 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | X0 = X9
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
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
        | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
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
        | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f43,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:28:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (14026)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.50  % (14026)Refutation not found, incomplete strategy% (14026)------------------------------
% 0.22/0.50  % (14026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (14026)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (14026)Memory used [KB]: 1663
% 0.22/0.50  % (14026)Time elapsed: 0.094 s
% 0.22/0.50  % (14026)------------------------------
% 0.22/0.50  % (14026)------------------------------
% 0.22/0.51  % (14034)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (14027)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (14025)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (14037)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (14028)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (14039)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (14043)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (14054)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (14045)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (14030)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (14043)Refutation not found, incomplete strategy% (14043)------------------------------
% 0.22/0.53  % (14043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14035)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (14047)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (14043)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14043)Memory used [KB]: 1791
% 0.22/0.53  % (14043)Time elapsed: 0.122 s
% 0.22/0.53  % (14043)------------------------------
% 0.22/0.53  % (14043)------------------------------
% 0.22/0.53  % (14053)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (14031)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (14036)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (14029)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (14038)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (14048)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (14052)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (14052)Refutation not found, incomplete strategy% (14052)------------------------------
% 0.22/0.53  % (14052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14052)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14052)Memory used [KB]: 6140
% 0.22/0.53  % (14052)Time elapsed: 0.128 s
% 0.22/0.54  % (14052)------------------------------
% 0.22/0.54  % (14052)------------------------------
% 0.22/0.54  % (14039)Refutation not found, incomplete strategy% (14039)------------------------------
% 0.22/0.54  % (14039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14040)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (14044)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (14039)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  % (14051)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  
% 0.22/0.54  % (14039)Memory used [KB]: 1791
% 0.22/0.54  % (14039)Time elapsed: 0.097 s
% 0.22/0.54  % (14039)------------------------------
% 0.22/0.54  % (14039)------------------------------
% 1.49/0.54  % (14032)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.49/0.55  % (14054)Refutation not found, incomplete strategy% (14054)------------------------------
% 1.49/0.55  % (14054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (14054)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (14054)Memory used [KB]: 1663
% 1.49/0.55  % (14054)Time elapsed: 0.003 s
% 1.49/0.55  % (14054)------------------------------
% 1.49/0.55  % (14054)------------------------------
% 1.49/0.55  % (14050)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.49/0.55  % (14042)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.49/0.55  % (14047)Refutation found. Thanks to Tanya!
% 1.49/0.55  % SZS status Theorem for theBenchmark
% 1.49/0.55  % SZS output start Proof for theBenchmark
% 1.49/0.55  fof(f285,plain,(
% 1.49/0.55    $false),
% 1.49/0.55    inference(unit_resulting_resolution,[],[f43,f99,f282])).
% 1.49/0.55  fof(f282,plain,(
% 1.49/0.55    ( ! [X0] : (~sP0(X0,sK2,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | sK3 = X0) )),
% 1.49/0.55    inference(resolution,[],[f273,f98])).
% 1.49/0.55  fof(f98,plain,(
% 1.49/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.49/0.55    inference(equality_resolution,[],[f93])).
% 1.49/0.55  fof(f93,plain,(
% 1.49/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.49/0.55    inference(definition_unfolding,[],[f53,f86])).
% 1.49/0.55  fof(f86,plain,(
% 1.49/0.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.49/0.55    inference(definition_unfolding,[],[f46,f85])).
% 1.49/0.55  fof(f85,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.49/0.55    inference(definition_unfolding,[],[f49,f84])).
% 1.49/0.55  fof(f84,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.49/0.55    inference(definition_unfolding,[],[f57,f83])).
% 1.49/0.55  fof(f83,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.49/0.55    inference(definition_unfolding,[],[f59,f82])).
% 1.49/0.55  fof(f82,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.49/0.55    inference(definition_unfolding,[],[f60,f81])).
% 1.49/0.55  fof(f81,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.49/0.55    inference(definition_unfolding,[],[f61,f62])).
% 1.49/0.55  fof(f62,plain,(
% 1.49/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f17])).
% 1.49/0.55  fof(f17,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.49/0.55  fof(f61,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f16])).
% 1.49/0.55  fof(f16,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.49/0.55  fof(f60,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f15])).
% 1.49/0.55  fof(f15,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.49/0.55  fof(f59,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f14])).
% 1.49/0.55  fof(f14,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.49/0.55  fof(f57,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f13])).
% 1.49/0.55  fof(f13,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.49/0.55  fof(f49,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f12])).
% 1.49/0.55  fof(f12,axiom,(
% 1.49/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.49/0.55  fof(f46,plain,(
% 1.49/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f11])).
% 1.49/0.55  fof(f11,axiom,(
% 1.49/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.49/0.55  fof(f53,plain,(
% 1.49/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.49/0.55    inference(cnf_transformation,[],[f33])).
% 1.49/0.55  fof(f33,plain,(
% 1.49/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 1.49/0.55  fof(f32,plain,(
% 1.49/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f31,plain,(
% 1.49/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.49/0.55    inference(rectify,[],[f30])).
% 1.49/0.56  fof(f30,plain,(
% 1.49/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.49/0.56    inference(nnf_transformation,[],[f8])).
% 1.49/0.56  fof(f8,axiom,(
% 1.49/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.49/0.56  fof(f273,plain,(
% 1.49/0.56    ( ! [X0] : (r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~sP0(X0,sK2,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) )),
% 1.49/0.56    inference(resolution,[],[f271,f65])).
% 1.49/0.56  fof(f65,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X11,X9)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f37])).
% 1.49/0.56  fof(f37,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ((~sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.49/0.56  fof(f36,plain,(
% 1.49/0.56    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9))) => ((~sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f35,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 1.49/0.56    inference(rectify,[],[f34])).
% 1.49/0.56  fof(f34,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 1.49/0.56    inference(nnf_transformation,[],[f26])).
% 1.49/0.56  % (14046)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.56  fof(f26,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) <=> ! [X10] : (r2_hidden(X10,X9) <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.49/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.49/0.56  fof(f271,plain,(
% 1.49/0.56    sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 1.49/0.56    inference(forward_demodulation,[],[f270,f45])).
% 1.49/0.56  fof(f45,plain,(
% 1.49/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.49/0.56  fof(f270,plain,(
% 1.49/0.56    sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0))),
% 1.49/0.56    inference(forward_demodulation,[],[f260,f44])).
% 1.49/0.56  fof(f44,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f6])).
% 1.49/0.56  fof(f6,axiom,(
% 1.49/0.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.49/0.56  fof(f260,plain,(
% 1.49/0.56    sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.49/0.56    inference(superposition,[],[f108,f110])).
% 1.49/0.56  fof(f110,plain,(
% 1.49/0.56    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 1.49/0.56    inference(resolution,[],[f88,f52])).
% 1.49/0.56  fof(f52,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f22])).
% 1.49/0.56  fof(f22,plain,(
% 1.49/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.49/0.56    inference(ennf_transformation,[],[f4])).
% 1.49/0.56  fof(f4,axiom,(
% 1.49/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.49/0.56  fof(f88,plain,(
% 1.49/0.56    r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 1.49/0.56    inference(definition_unfolding,[],[f42,f86,f86])).
% 1.49/0.56  fof(f42,plain,(
% 1.49/0.56    r1_tarski(k1_tarski(sK2),k1_tarski(sK3))),
% 1.49/0.56    inference(cnf_transformation,[],[f29])).
% 1.49/0.56  fof(f29,plain,(
% 1.49/0.56    sK2 != sK3 & r1_tarski(k1_tarski(sK2),k1_tarski(sK3))),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f28])).
% 1.49/0.56  fof(f28,plain,(
% 1.49/0.56    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK2 != sK3 & r1_tarski(k1_tarski(sK2),k1_tarski(sK3)))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f21,plain,(
% 1.49/0.56    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.49/0.56    inference(ennf_transformation,[],[f20])).
% 1.49/0.56  fof(f20,negated_conjecture,(
% 1.49/0.56    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.49/0.56    inference(negated_conjecture,[],[f19])).
% 1.49/0.56  fof(f19,conjecture,(
% 1.49/0.56    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).
% 1.49/0.56  fof(f108,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))))) )),
% 1.49/0.56    inference(equality_resolution,[],[f95])).
% 1.49/0.56  fof(f95,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) != X9) )),
% 1.49/0.56    inference(definition_unfolding,[],[f78,f87])).
% 1.49/0.56  fof(f87,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f63,f80,f86])).
% 1.49/0.56  fof(f80,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f50,f51])).
% 1.49/0.56  fof(f51,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f2])).
% 1.49/0.56  fof(f2,axiom,(
% 1.49/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.49/0.56  fof(f50,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,axiom,(
% 1.49/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.49/0.56  fof(f63,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f10])).
% 1.49/0.56  fof(f10,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).
% 1.49/0.56  fof(f78,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 1.49/0.56    inference(cnf_transformation,[],[f41])).
% 1.49/0.56  fof(f41,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 1.49/0.56    inference(nnf_transformation,[],[f27])).
% 1.49/0.56  fof(f27,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9))),
% 1.49/0.56    inference(definition_folding,[],[f24,f26,f25])).
% 1.49/0.56  fof(f25,plain,(
% 1.49/0.56    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10))),
% 1.49/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.49/0.56  fof(f24,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 1.49/0.56    inference(ennf_transformation,[],[f9])).
% 1.49/0.56  fof(f9,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).
% 1.49/0.56  fof(f99,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 1.49/0.56    inference(equality_resolution,[],[f77])).
% 1.49/0.56  fof(f77,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X1) )),
% 1.49/0.56    inference(cnf_transformation,[],[f40])).
% 1.49/0.56  fof(f40,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8 & X0 != X9)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 1.49/0.56    inference(rectify,[],[f39])).
% 1.49/0.56  fof(f39,plain,(
% 1.49/0.56    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.49/0.56    inference(flattening,[],[f38])).
% 1.49/0.56  fof(f38,plain,(
% 1.49/0.56    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.49/0.56    inference(nnf_transformation,[],[f25])).
% 1.49/0.56  fof(f43,plain,(
% 1.49/0.56    sK2 != sK3),
% 1.49/0.56    inference(cnf_transformation,[],[f29])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (14047)------------------------------
% 1.49/0.56  % (14047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (14047)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (14047)Memory used [KB]: 6524
% 1.49/0.56  % (14047)Time elapsed: 0.106 s
% 1.49/0.56  % (14047)------------------------------
% 1.49/0.56  % (14047)------------------------------
% 1.49/0.56  % (14024)Success in time 0.201 s
%------------------------------------------------------------------------------
