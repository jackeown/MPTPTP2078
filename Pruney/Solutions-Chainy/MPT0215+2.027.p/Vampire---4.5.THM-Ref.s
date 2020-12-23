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
% DateTime   : Thu Dec  3 12:35:11 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 342 expanded)
%              Number of leaves         :   16 ( 115 expanded)
%              Depth                    :   14
%              Number of atoms          :  321 ( 923 expanded)
%              Number of equality atoms :  270 ( 830 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f121,f152,f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | ~ sP0(X0,X1,X2,X11,X4,X5,X6,X7,X8,X9) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X3 != X11
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
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

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f152,plain,(
    ! [X2,X1] : sP0(X1,X2,sK3,sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,X2,X1)) ),
    inference(forward_demodulation,[],[f151,f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) ),
    inference(definition_unfolding,[],[f37,f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f38,f62,f67])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f34,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f151,plain,(
    ! [X2,X1] : sP0(X1,X2,sK3,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X2),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X2))))) ),
    inference(forward_demodulation,[],[f148,f70])).

fof(f148,plain,(
    ! [X2,X1] : sP0(X1,X2,sK3,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k3_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k3_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))))) ),
    inference(superposition,[],[f83,f71])).

fof(f71,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f27,f67,f66])).

fof(f27,plain,(
    k1_tarski(sK1) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK1 != sK2
    & k1_tarski(sK1) = k2_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f19])).

% (25905)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK1 != sK2
      & k1_tarski(sK1) = k2_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))))))) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
      | k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))))) != X9 ) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))))) ),
    inference(definition_unfolding,[],[f39,f62,f68,f67])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ~ sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) )
      & ( sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) ) ),
    inference(definition_folding,[],[f16,f17])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f121,plain,(
    ~ r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f120,f70])).

fof(f120,plain,(
    ~ r2_hidden(sK2,k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    inference(forward_demodulation,[],[f92,f70])).

fof(f92,plain,(
    ~ r2_hidden(sK2,k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))))) ),
    inference(unit_resulting_resolution,[],[f28,f28,f28,f28,f28,f28,f28,f83,f28,f28,f40])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( X0 = X11
      | X1 = X11
      | X2 = X11
      | X3 = X11
      | X4 = X11
      | X5 = X11
      | X6 = X11
      | X7 = X11
      | X8 = X11
      | ~ r2_hidden(X11,X9)
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f28,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.49  % (25897)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (25891)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (25893)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (25898)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (25898)Refutation not found, incomplete strategy% (25898)------------------------------
% 0.22/0.53  % (25898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25898)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25898)Memory used [KB]: 10618
% 0.22/0.53  % (25898)Time elapsed: 0.106 s
% 0.22/0.53  % (25898)------------------------------
% 0.22/0.53  % (25898)------------------------------
% 0.22/0.53  % (25894)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (25890)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (25918)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (25906)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (25907)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (25916)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (25901)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (25906)Refutation not found, incomplete strategy% (25906)------------------------------
% 0.22/0.53  % (25906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25909)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (25889)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (25906)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25906)Memory used [KB]: 10618
% 0.22/0.53  % (25906)Time elapsed: 0.118 s
% 0.22/0.53  % (25906)------------------------------
% 0.22/0.53  % (25906)------------------------------
% 0.22/0.53  % (25892)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (25889)Refutation not found, incomplete strategy% (25889)------------------------------
% 0.22/0.53  % (25889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25889)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25889)Memory used [KB]: 1663
% 0.22/0.53  % (25889)Time elapsed: 0.126 s
% 0.22/0.53  % (25889)------------------------------
% 0.22/0.53  % (25889)------------------------------
% 0.22/0.53  % (25900)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (25908)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (25900)Refutation not found, incomplete strategy% (25900)------------------------------
% 0.22/0.54  % (25900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25900)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (25900)Memory used [KB]: 10618
% 0.22/0.54  % (25900)Time elapsed: 0.095 s
% 0.22/0.54  % (25900)------------------------------
% 0.22/0.54  % (25900)------------------------------
% 0.22/0.54  % (25902)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (25909)Refutation not found, incomplete strategy% (25909)------------------------------
% 0.22/0.54  % (25909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25909)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (25909)Memory used [KB]: 10746
% 0.22/0.54  % (25909)Time elapsed: 0.127 s
% 0.22/0.54  % (25909)------------------------------
% 0.22/0.54  % (25909)------------------------------
% 0.22/0.54  % (25899)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (25899)Refutation not found, incomplete strategy% (25899)------------------------------
% 0.22/0.54  % (25899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25899)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (25899)Memory used [KB]: 10618
% 0.22/0.54  % (25899)Time elapsed: 0.135 s
% 0.22/0.54  % (25899)------------------------------
% 0.22/0.54  % (25899)------------------------------
% 0.22/0.54  % (25912)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (25915)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (25917)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (25896)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (25910)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (25911)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (25895)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.52/0.55  % (25913)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.52/0.55  % (25904)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.52/0.56  % (25903)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.52/0.56  % (25912)Refutation not found, incomplete strategy% (25912)------------------------------
% 1.52/0.56  % (25912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (25912)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (25912)Memory used [KB]: 1791
% 1.52/0.56  % (25912)Time elapsed: 0.159 s
% 1.52/0.56  % (25912)------------------------------
% 1.52/0.56  % (25912)------------------------------
% 1.66/0.57  % (25914)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.66/0.57  % (25915)Refutation found. Thanks to Tanya!
% 1.66/0.57  % SZS status Theorem for theBenchmark
% 1.66/0.57  % SZS output start Proof for theBenchmark
% 1.66/0.57  fof(f177,plain,(
% 1.66/0.57    $false),
% 1.66/0.57    inference(unit_resulting_resolution,[],[f121,f152,f77])).
% 1.66/0.57  fof(f77,plain,(
% 1.66/0.57    ( ! [X6,X4,X2,X0,X8,X7,X5,X1,X11,X9] : (r2_hidden(X11,X9) | ~sP0(X0,X1,X2,X11,X4,X5,X6,X7,X8,X9)) )),
% 1.66/0.57    inference(equality_resolution,[],[f46])).
% 1.66/0.57  fof(f46,plain,(
% 1.66/0.57    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X3 != X11 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f25])).
% 1.66/0.57  fof(f25,plain,(
% 1.66/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (((sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X0 != X11 & X1 != X11 & X2 != X11 & X3 != X11 & X4 != X11 & X5 != X11 & X6 != X11 & X7 != X11 & X8 != X11)) & (X0 = X11 | X1 = X11 | X2 = X11 | X3 = X11 | X4 = X11 | X5 = X11 | X6 = X11 | X7 = X11 | X8 = X11 | ~r2_hidden(X11,X9))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 1.66/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 1.66/0.57  fof(f24,plain,(
% 1.66/0.57    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : (((X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10 & X8 != X10) | ~r2_hidden(X10,X9)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | X8 = X10 | r2_hidden(X10,X9))) => (((sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 1.66/0.57    introduced(choice_axiom,[])).
% 1.66/0.57  fof(f23,plain,(
% 1.66/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : (((X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10 & X8 != X10) | ~r2_hidden(X10,X9)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | X8 = X10 | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X0 != X11 & X1 != X11 & X2 != X11 & X3 != X11 & X4 != X11 & X5 != X11 & X6 != X11 & X7 != X11 & X8 != X11)) & (X0 = X11 | X1 = X11 | X2 = X11 | X3 = X11 | X4 = X11 | X5 = X11 | X6 = X11 | X7 = X11 | X8 = X11 | ~r2_hidden(X11,X9))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 1.66/0.57    inference(rectify,[],[f22])).
% 1.66/0.57  fof(f22,plain,(
% 1.66/0.57    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0,X9] : ((sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X9))) | ~sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)))),
% 1.66/0.57    inference(flattening,[],[f21])).
% 1.66/0.57  fof(f21,plain,(
% 1.66/0.57    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0,X9] : ((sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~r2_hidden(X10,X9))) | ~sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)))),
% 1.66/0.57    inference(nnf_transformation,[],[f17])).
% 1.66/0.57  fof(f17,plain,(
% 1.66/0.57    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0,X9] : (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 1.66/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.66/0.57  fof(f152,plain,(
% 1.66/0.57    ( ! [X2,X1] : (sP0(X1,X2,sK3,sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,X2,X1))) )),
% 1.66/0.57    inference(forward_demodulation,[],[f151,f70])).
% 1.66/0.57  fof(f70,plain,(
% 1.66/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))))) )),
% 1.66/0.57    inference(definition_unfolding,[],[f37,f68])).
% 1.66/0.57  fof(f68,plain,(
% 1.66/0.57    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))) )),
% 1.66/0.57    inference(definition_unfolding,[],[f38,f62,f67])).
% 1.66/0.57  fof(f67,plain,(
% 1.66/0.57    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.66/0.57    inference(definition_unfolding,[],[f29,f66])).
% 1.66/0.57  fof(f66,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.66/0.57    inference(definition_unfolding,[],[f30,f65])).
% 1.66/0.57  fof(f65,plain,(
% 1.66/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.66/0.57    inference(definition_unfolding,[],[f33,f64])).
% 1.66/0.57  fof(f64,plain,(
% 1.66/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.66/0.57    inference(definition_unfolding,[],[f34,f63])).
% 1.66/0.57  fof(f63,plain,(
% 1.66/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.66/0.57    inference(definition_unfolding,[],[f35,f36])).
% 1.66/0.57  fof(f36,plain,(
% 1.66/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f11])).
% 1.66/0.57  fof(f11,axiom,(
% 1.66/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.66/0.57  fof(f35,plain,(
% 1.66/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f10])).
% 1.66/0.57  fof(f10,axiom,(
% 1.66/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.66/0.57  fof(f34,plain,(
% 1.66/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f9])).
% 1.66/0.57  fof(f9,axiom,(
% 1.66/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.66/0.57  fof(f33,plain,(
% 1.66/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f8])).
% 1.66/0.57  fof(f8,axiom,(
% 1.66/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.66/0.57  fof(f30,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f7])).
% 1.66/0.57  fof(f7,axiom,(
% 1.66/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.66/0.57  fof(f29,plain,(
% 1.66/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f6])).
% 1.66/0.57  fof(f6,axiom,(
% 1.66/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.66/0.57  fof(f62,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.66/0.57    inference(definition_unfolding,[],[f32,f31])).
% 1.66/0.57  fof(f31,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.66/0.57    inference(cnf_transformation,[],[f1])).
% 1.66/0.57  fof(f1,axiom,(
% 1.66/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.66/0.57  fof(f32,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.66/0.57    inference(cnf_transformation,[],[f2])).
% 1.66/0.57  fof(f2,axiom,(
% 1.66/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.66/0.57  fof(f38,plain,(
% 1.66/0.57    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 1.66/0.57    inference(cnf_transformation,[],[f5])).
% 1.66/0.57  fof(f5,axiom,(
% 1.66/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 1.66/0.57  fof(f37,plain,(
% 1.66/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f12])).
% 1.66/0.57  fof(f12,axiom,(
% 1.66/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.66/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.66/0.57  fof(f151,plain,(
% 1.66/0.57    ( ! [X2,X1] : (sP0(X1,X2,sK3,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X2),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X2)))))) )),
% 1.66/0.57    inference(forward_demodulation,[],[f148,f70])).
% 1.66/0.57  fof(f148,plain,(
% 1.66/0.57    ( ! [X2,X1] : (sP0(X1,X2,sK3,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k3_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k3_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))))) )),
% 1.66/0.57    inference(superposition,[],[f83,f71])).
% 1.66/0.57  fof(f71,plain,(
% 1.66/0.57    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 1.66/0.57    inference(definition_unfolding,[],[f27,f67,f66])).
% 1.66/0.57  fof(f27,plain,(
% 1.66/0.57    k1_tarski(sK1) = k2_tarski(sK2,sK3)),
% 1.66/0.57    inference(cnf_transformation,[],[f20])).
% 1.66/0.57  fof(f20,plain,(
% 1.66/0.57    sK1 != sK2 & k1_tarski(sK1) = k2_tarski(sK2,sK3)),
% 1.66/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f19])).
% 1.66/0.57  % (25905)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.66/0.58  fof(f19,plain,(
% 1.66/0.58    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK1 != sK2 & k1_tarski(sK1) = k2_tarski(sK2,sK3))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f15,plain,(
% 1.66/0.58    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 1.66/0.58    inference(ennf_transformation,[],[f14])).
% 1.66/0.58  fof(f14,negated_conjecture,(
% 1.66/0.58    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 1.66/0.58    inference(negated_conjecture,[],[f13])).
% 1.66/0.58  fof(f13,conjecture,(
% 1.66/0.58    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).
% 1.66/0.58  fof(f83,plain,(
% 1.66/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))))))) )),
% 1.66/0.58    inference(equality_resolution,[],[f73])).
% 1.66/0.58  fof(f73,plain,(
% 1.66/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))))) != X9) )),
% 1.66/0.58    inference(definition_unfolding,[],[f60,f69])).
% 1.66/0.58  fof(f69,plain,(
% 1.66/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))),k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))))))) )),
% 1.66/0.58    inference(definition_unfolding,[],[f39,f62,f68,f67])).
% 1.66/0.58  fof(f39,plain,(
% 1.66/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f4])).
% 1.66/0.58  fof(f4,axiom,(
% 1.66/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).
% 1.66/0.58  fof(f60,plain,(
% 1.66/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 1.66/0.58    inference(cnf_transformation,[],[f26])).
% 1.66/0.58  fof(f26,plain,(
% 1.66/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ~sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)) & (sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 1.66/0.58    inference(nnf_transformation,[],[f18])).
% 1.66/0.58  fof(f18,plain,(
% 1.66/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> sP0(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9))),
% 1.66/0.58    inference(definition_folding,[],[f16,f17])).
% 1.66/0.58  fof(f16,plain,(
% 1.66/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 1.66/0.58    inference(ennf_transformation,[],[f3])).
% 1.66/0.58  fof(f3,axiom,(
% 1.66/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).
% 1.66/0.58  fof(f121,plain,(
% 1.66/0.58    ~r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.66/0.58    inference(forward_demodulation,[],[f120,f70])).
% 1.66/0.58  fof(f120,plain,(
% 1.66/0.58    ~r2_hidden(sK2,k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))),
% 1.66/0.58    inference(forward_demodulation,[],[f92,f70])).
% 1.66/0.58  fof(f92,plain,(
% 1.66/0.58    ~r2_hidden(sK2,k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))))),
% 1.66/0.58    inference(unit_resulting_resolution,[],[f28,f28,f28,f28,f28,f28,f28,f83,f28,f28,f40])).
% 1.66/0.58  fof(f40,plain,(
% 1.66/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (X0 = X11 | X1 = X11 | X2 = X11 | X3 = X11 | X4 = X11 | X5 = X11 | X6 = X11 | X7 = X11 | X8 = X11 | ~r2_hidden(X11,X9) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f25])).
% 1.66/0.58  fof(f28,plain,(
% 1.66/0.58    sK1 != sK2),
% 1.66/0.58    inference(cnf_transformation,[],[f20])).
% 1.66/0.58  % SZS output end Proof for theBenchmark
% 1.66/0.58  % (25915)------------------------------
% 1.66/0.58  % (25915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (25915)Termination reason: Refutation
% 1.66/0.58  
% 1.66/0.58  % (25915)Memory used [KB]: 11001
% 1.66/0.58  % (25915)Time elapsed: 0.174 s
% 1.66/0.58  % (25915)------------------------------
% 1.66/0.58  % (25915)------------------------------
% 1.66/0.58  % (25910)Refutation not found, incomplete strategy% (25910)------------------------------
% 1.66/0.58  % (25910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (25888)Success in time 0.218 s
%------------------------------------------------------------------------------
