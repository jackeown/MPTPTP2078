%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:23 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 299 expanded)
%              Number of leaves         :   23 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          :  428 ( 671 expanded)
%              Number of equality atoms :  331 ( 552 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f341,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f178,f183,f192,f337,f340])).

fof(f340,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | spl6_10 ),
    inference(subsumption_resolution,[],[f338,f301])).

fof(f301,plain,(
    ! [X26,X24,X23,X21,X27,X25,X22] : r2_hidden(X24,k6_enumset1(X21,X21,X22,X23,X24,X25,X26,X27)) ),
    inference(superposition,[],[f162,f107])).

fof(f107,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f74,f99,f104,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f100])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f99,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

fof(f162,plain,(
    ! [X6,X4,X2,X0,X8,X7,X3,X1,X11] : r2_hidden(X11,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X11,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X11,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
    inference(equality_resolution,[],[f161])).

fof(f161,plain,(
    ! [X6,X4,X2,X0,X8,X7,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X11,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X11,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9 ) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X5 != X11
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9 ) ),
    inference(definition_unfolding,[],[f85,f106])).

fof(f106,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f76,f99,f105])).

fof(f105,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f104])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X5 != X11
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ( ( ( sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
          & ( sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ( X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 ) )
            & ( X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | ~ r2_hidden(X11,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X10] :
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
            | r2_hidden(X10,X9) ) )
     => ( ( ( sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
        & ( sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
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
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ( X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 ) )
            & ( X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | ~ r2_hidden(X11,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
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
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
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
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f338,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3))
    | spl6_10 ),
    inference(forward_demodulation,[],[f336,f307])).

fof(f307,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X1,X2,X2,X2,X2,X2,X3) ),
    inference(superposition,[],[f122,f107])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f70,f102,f99,f104,f104])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f336,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK1,sK2,sK2,sK2,sK2,sK2,sK3))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl6_10
  <=> r2_hidden(sK0,k6_enumset1(sK0,sK1,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f337,plain,
    ( ~ spl6_10
    | spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f227,f189,f180,f175,f334])).

fof(f175,plain,
    ( spl6_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f180,plain,
    ( spl6_2
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f189,plain,
    ( spl6_3
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f227,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK1,sK2,sK2,sK2,sK2,sK2,sK3))
    | spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f214,f197])).

fof(f197,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK0,sK1,sK2,sK2,sK2,sK2,sK2,sK3)
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f193,f107])).

fof(f193,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f191,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ) ),
    inference(definition_unfolding,[],[f55,f99])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f191,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f189])).

fof(f214,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f182,f177,f150])).

fof(f150,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f104])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f177,plain,
    ( sK0 != sK2
    | spl6_1 ),
    inference(avatar_component_clause,[],[f175])).

fof(f182,plain,
    ( sK0 != sK3
    | spl6_2 ),
    inference(avatar_component_clause,[],[f180])).

fof(f192,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f108,f189])).

fof(f108,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f45,f104,f104])).

fof(f45,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f183,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f47,f180])).

fof(f47,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f178,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f46,f175])).

fof(f46,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:32:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (18841)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (18834)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (18842)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (18842)Refutation not found, incomplete strategy% (18842)------------------------------
% 0.20/0.51  % (18842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (18827)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (18835)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (18842)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (18842)Memory used [KB]: 10746
% 0.20/0.51  % (18842)Time elapsed: 0.093 s
% 0.20/0.51  % (18842)------------------------------
% 0.20/0.51  % (18842)------------------------------
% 0.20/0.51  % (18830)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (18827)Refutation not found, incomplete strategy% (18827)------------------------------
% 0.20/0.51  % (18827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (18827)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (18827)Memory used [KB]: 1663
% 0.20/0.51  % (18827)Time elapsed: 0.101 s
% 0.20/0.51  % (18827)------------------------------
% 0.20/0.51  % (18827)------------------------------
% 1.25/0.52  % (18850)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.25/0.52  % (18848)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.25/0.53  % (18838)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.25/0.53  % (18838)Refutation not found, incomplete strategy% (18838)------------------------------
% 1.25/0.53  % (18838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (18838)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (18838)Memory used [KB]: 10618
% 1.25/0.53  % (18838)Time elapsed: 0.133 s
% 1.25/0.53  % (18838)------------------------------
% 1.25/0.53  % (18838)------------------------------
% 1.39/0.53  % (18829)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.39/0.53  % (18852)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.53  % (18839)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.53  % (18840)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.39/0.53  % (18831)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.39/0.54  % (18833)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.54  % (18855)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.54  % (18855)Refutation not found, incomplete strategy% (18855)------------------------------
% 1.39/0.54  % (18855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (18855)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (18855)Memory used [KB]: 1663
% 1.39/0.54  % (18855)Time elapsed: 0.001 s
% 1.39/0.54  % (18855)------------------------------
% 1.39/0.54  % (18855)------------------------------
% 1.39/0.54  % (18832)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.54  % (18853)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.39/0.54  % (18846)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.54  % (18826)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.39/0.54  % (18844)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.54  % (18847)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.55  % (18854)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.39/0.55  % (18837)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.39/0.55  % (18845)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.55  % (18851)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.55  % (18849)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.55  % (18828)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.56  % (18843)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.57  % (18836)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.57  % (18846)Refutation found. Thanks to Tanya!
% 1.39/0.57  % SZS status Theorem for theBenchmark
% 1.39/0.57  % SZS output start Proof for theBenchmark
% 1.39/0.57  fof(f341,plain,(
% 1.39/0.57    $false),
% 1.39/0.57    inference(avatar_sat_refutation,[],[f178,f183,f192,f337,f340])).
% 1.39/0.57  fof(f340,plain,(
% 1.39/0.57    spl6_10),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f339])).
% 1.39/0.57  fof(f339,plain,(
% 1.39/0.57    $false | spl6_10),
% 1.39/0.57    inference(subsumption_resolution,[],[f338,f301])).
% 1.39/0.57  fof(f301,plain,(
% 1.39/0.57    ( ! [X26,X24,X23,X21,X27,X25,X22] : (r2_hidden(X24,k6_enumset1(X21,X21,X22,X23,X24,X25,X26,X27))) )),
% 1.39/0.57    inference(superposition,[],[f162,f107])).
% 1.39/0.57  fof(f107,plain,(
% 1.39/0.57    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.39/0.57    inference(definition_unfolding,[],[f74,f99,f104,f100])).
% 1.39/0.57  fof(f100,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.39/0.57    inference(definition_unfolding,[],[f72,f73])).
% 1.39/0.57  fof(f73,plain,(
% 1.39/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f22])).
% 1.39/0.57  fof(f22,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.39/0.57  fof(f72,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f21])).
% 1.39/0.57  fof(f21,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.39/0.57  fof(f104,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.39/0.57    inference(definition_unfolding,[],[f51,f103])).
% 1.39/0.57  fof(f103,plain,(
% 1.39/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.39/0.57    inference(definition_unfolding,[],[f56,f102])).
% 1.39/0.57  fof(f102,plain,(
% 1.39/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.39/0.57    inference(definition_unfolding,[],[f69,f101])).
% 1.39/0.57  fof(f101,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.39/0.57    inference(definition_unfolding,[],[f71,f100])).
% 1.39/0.57  fof(f71,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f20])).
% 1.39/0.57  fof(f20,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.39/0.57  fof(f69,plain,(
% 1.39/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f19])).
% 1.39/0.57  fof(f19,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.39/0.57  fof(f56,plain,(
% 1.39/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f18])).
% 1.39/0.57  fof(f18,axiom,(
% 1.39/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.39/0.57  fof(f51,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f17])).
% 1.39/0.57  fof(f17,axiom,(
% 1.39/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.57  fof(f99,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.39/0.57    inference(definition_unfolding,[],[f53,f52])).
% 1.39/0.57  fof(f52,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.39/0.57    inference(cnf_transformation,[],[f1])).
% 1.39/0.57  fof(f1,axiom,(
% 1.39/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.39/0.57  fof(f53,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.39/0.57    inference(cnf_transformation,[],[f6])).
% 1.39/0.57  fof(f6,axiom,(
% 1.39/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.39/0.57  fof(f74,plain,(
% 1.39/0.57    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) )),
% 1.39/0.57    inference(cnf_transformation,[],[f14])).
% 1.39/0.57  fof(f14,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
% 1.39/0.57  fof(f162,plain,(
% 1.39/0.57    ( ! [X6,X4,X2,X0,X8,X7,X3,X1,X11] : (r2_hidden(X11,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X11,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X11,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) )),
% 1.39/0.57    inference(equality_resolution,[],[f161])).
% 1.39/0.57  fof(f161,plain,(
% 1.39/0.57    ( ! [X6,X4,X2,X0,X8,X7,X3,X1,X11,X9] : (r2_hidden(X11,X9) | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X11,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X11,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9) )),
% 1.39/0.57    inference(equality_resolution,[],[f139])).
% 1.39/0.58  fof(f139,plain,(
% 1.39/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X5 != X11 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9) )),
% 1.39/0.58    inference(definition_unfolding,[],[f85,f106])).
% 1.39/0.58  fof(f106,plain,(
% 1.39/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 1.39/0.58    inference(definition_unfolding,[],[f76,f99,f105])).
% 1.39/0.58  fof(f105,plain,(
% 1.39/0.58    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.39/0.58    inference(definition_unfolding,[],[f50,f104])).
% 1.39/0.58  fof(f50,plain,(
% 1.39/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f16])).
% 1.39/0.58  fof(f16,axiom,(
% 1.39/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.39/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.58  fof(f76,plain,(
% 1.39/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 1.39/0.58    inference(cnf_transformation,[],[f11])).
% 1.39/0.58  fof(f11,axiom,(
% 1.39/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 1.39/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).
% 1.39/0.58  fof(f85,plain,(
% 1.39/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X5 != X11 | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 1.39/0.58    inference(cnf_transformation,[],[f44])).
% 1.39/0.58  fof(f44,plain,(
% 1.39/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | (((sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 1.39/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 1.39/0.58  fof(f43,plain,(
% 1.39/0.58    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9))) => (((sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 1.39/0.58    introduced(choice_axiom,[])).
% 1.39/0.58  fof(f42,plain,(
% 1.39/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 1.39/0.58    inference(rectify,[],[f41])).
% 1.39/0.58  fof(f41,plain,(
% 1.39/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 1.39/0.58    inference(flattening,[],[f40])).
% 1.39/0.60  fof(f40,plain,(
% 1.39/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~r2_hidden(X10,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 1.39/0.60    inference(nnf_transformation,[],[f30])).
% 1.39/0.60  fof(f30,plain,(
% 1.39/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 1.39/0.60    inference(ennf_transformation,[],[f8])).
% 1.39/0.60  fof(f8,axiom,(
% 1.39/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 1.39/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).
% 1.39/0.60  fof(f338,plain,(
% 1.39/0.60    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3)) | spl6_10),
% 1.39/0.60    inference(forward_demodulation,[],[f336,f307])).
% 1.39/0.60  fof(f307,plain,(
% 1.39/0.60    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X1,X2,X2,X2,X2,X2,X3)) )),
% 1.39/0.60    inference(superposition,[],[f122,f107])).
% 1.39/0.60  fof(f122,plain,(
% 1.39/0.60    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.39/0.60    inference(definition_unfolding,[],[f70,f102,f99,f104,f104])).
% 1.39/0.60  fof(f70,plain,(
% 1.39/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.39/0.60    inference(cnf_transformation,[],[f9])).
% 1.39/0.60  fof(f9,axiom,(
% 1.39/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.39/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 1.39/0.60  fof(f336,plain,(
% 1.39/0.60    ~r2_hidden(sK0,k6_enumset1(sK0,sK1,sK2,sK2,sK2,sK2,sK2,sK3)) | spl6_10),
% 1.39/0.60    inference(avatar_component_clause,[],[f334])).
% 1.39/0.60  fof(f334,plain,(
% 1.39/0.60    spl6_10 <=> r2_hidden(sK0,k6_enumset1(sK0,sK1,sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.39/0.60  fof(f337,plain,(
% 1.39/0.60    ~spl6_10 | spl6_1 | spl6_2 | ~spl6_3),
% 1.39/0.60    inference(avatar_split_clause,[],[f227,f189,f180,f175,f334])).
% 1.39/0.60  fof(f175,plain,(
% 1.39/0.60    spl6_1 <=> sK0 = sK2),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.39/0.60  fof(f180,plain,(
% 1.39/0.60    spl6_2 <=> sK0 = sK3),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.39/0.60  fof(f189,plain,(
% 1.39/0.60    spl6_3 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.39/0.60  fof(f227,plain,(
% 1.39/0.60    ~r2_hidden(sK0,k6_enumset1(sK0,sK1,sK2,sK2,sK2,sK2,sK2,sK3)) | (spl6_1 | spl6_2 | ~spl6_3)),
% 1.39/0.60    inference(forward_demodulation,[],[f214,f197])).
% 1.39/0.60  fof(f197,plain,(
% 1.39/0.60    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK0,sK1,sK2,sK2,sK2,sK2,sK2,sK3) | ~spl6_3),
% 1.39/0.60    inference(forward_demodulation,[],[f193,f107])).
% 1.39/0.60  fof(f193,plain,(
% 1.39/0.60    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~spl6_3),
% 1.39/0.60    inference(unit_resulting_resolution,[],[f191,f109])).
% 1.39/0.60  fof(f109,plain,(
% 1.39/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1) )),
% 1.39/0.60    inference(definition_unfolding,[],[f55,f99])).
% 1.39/0.60  fof(f55,plain,(
% 1.39/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f28])).
% 1.39/0.60  fof(f28,plain,(
% 1.39/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.39/0.60    inference(ennf_transformation,[],[f2])).
% 1.39/0.60  fof(f2,axiom,(
% 1.39/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.39/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.39/0.60  fof(f191,plain,(
% 1.39/0.60    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl6_3),
% 1.39/0.60    inference(avatar_component_clause,[],[f189])).
% 1.39/0.60  fof(f214,plain,(
% 1.39/0.60    ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | (spl6_1 | spl6_2)),
% 1.39/0.60    inference(unit_resulting_resolution,[],[f182,f177,f150])).
% 1.39/0.60  fof(f150,plain,(
% 1.39/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.39/0.60    inference(equality_resolution,[],[f115])).
% 1.39/0.60  fof(f115,plain,(
% 1.39/0.60    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.39/0.60    inference(definition_unfolding,[],[f57,f104])).
% 1.39/0.60  fof(f57,plain,(
% 1.39/0.60    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.39/0.60    inference(cnf_transformation,[],[f37])).
% 1.39/0.60  fof(f37,plain,(
% 1.39/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.39/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 1.39/0.60  fof(f36,plain,(
% 1.39/0.60    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.39/0.60    introduced(choice_axiom,[])).
% 1.39/0.60  fof(f35,plain,(
% 1.39/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.39/0.60    inference(rectify,[],[f34])).
% 1.39/0.60  fof(f34,plain,(
% 1.39/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.39/0.60    inference(flattening,[],[f33])).
% 1.39/0.60  fof(f33,plain,(
% 1.39/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.39/0.60    inference(nnf_transformation,[],[f7])).
% 1.39/0.60  fof(f7,axiom,(
% 1.39/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.39/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.39/0.60  fof(f177,plain,(
% 1.39/0.60    sK0 != sK2 | spl6_1),
% 1.39/0.60    inference(avatar_component_clause,[],[f175])).
% 1.39/0.60  fof(f182,plain,(
% 1.39/0.60    sK0 != sK3 | spl6_2),
% 1.39/0.60    inference(avatar_component_clause,[],[f180])).
% 1.39/0.60  fof(f192,plain,(
% 1.39/0.60    spl6_3),
% 1.39/0.60    inference(avatar_split_clause,[],[f108,f189])).
% 1.39/0.60  fof(f108,plain,(
% 1.39/0.60    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.39/0.60    inference(definition_unfolding,[],[f45,f104,f104])).
% 1.39/0.60  fof(f45,plain,(
% 1.39/0.60    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.39/0.60    inference(cnf_transformation,[],[f32])).
% 1.39/0.60  fof(f32,plain,(
% 1.39/0.60    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.39/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f31])).
% 1.39/0.60  fof(f31,plain,(
% 1.39/0.60    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 1.39/0.60    introduced(choice_axiom,[])).
% 1.39/0.60  fof(f26,plain,(
% 1.39/0.60    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.39/0.60    inference(ennf_transformation,[],[f25])).
% 1.39/0.60  fof(f25,negated_conjecture,(
% 1.39/0.60    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.39/0.60    inference(negated_conjecture,[],[f24])).
% 1.39/0.60  fof(f24,conjecture,(
% 1.39/0.60    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.39/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.39/0.60  fof(f183,plain,(
% 1.39/0.60    ~spl6_2),
% 1.39/0.60    inference(avatar_split_clause,[],[f47,f180])).
% 1.39/0.60  fof(f47,plain,(
% 1.39/0.60    sK0 != sK3),
% 1.39/0.60    inference(cnf_transformation,[],[f32])).
% 1.39/0.60  fof(f178,plain,(
% 1.39/0.60    ~spl6_1),
% 1.39/0.60    inference(avatar_split_clause,[],[f46,f175])).
% 1.39/0.60  fof(f46,plain,(
% 1.39/0.60    sK0 != sK2),
% 1.39/0.60    inference(cnf_transformation,[],[f32])).
% 1.39/0.60  % SZS output end Proof for theBenchmark
% 1.39/0.60  % (18846)------------------------------
% 1.39/0.60  % (18846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.60  % (18846)Termination reason: Refutation
% 1.39/0.60  
% 1.39/0.60  % (18846)Memory used [KB]: 11257
% 1.39/0.60  % (18846)Time elapsed: 0.175 s
% 1.39/0.60  % (18846)------------------------------
% 1.39/0.60  % (18846)------------------------------
% 1.39/0.60  % (18825)Success in time 0.243 s
%------------------------------------------------------------------------------
