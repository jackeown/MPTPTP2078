%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:26 EST 2020

% Result     : Theorem 2.81s
% Output     : Refutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 297 expanded)
%              Number of leaves         :   27 ( 101 expanded)
%              Depth                    :   16
%              Number of atoms          :  441 ( 651 expanded)
%              Number of equality atoms :  275 ( 462 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f741,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f151,f219,f228,f645,f740])).

fof(f740,plain,
    ( spl4_1
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f739])).

fof(f739,plain,
    ( $false
    | spl4_1
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f694,f150])).

fof(f150,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f694,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f648,f333])).

fof(f333,plain,(
    ! [X61,X59,X57,X62,X60,X58,X56,X63] : r2_hidden(X56,k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63)) ),
    inference(superposition,[],[f143,f93])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) ),
    inference(definition_unfolding,[],[f63,f90,f62,f91])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f89])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f143,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X11] : r2_hidden(X11,k3_tarski(k6_enumset1(k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8)))) ),
    inference(equality_resolution,[],[f142])).

fof(f142,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X11,X9] :
      ( r2_hidden(X11,X9)
      | k3_tarski(k6_enumset1(k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) != X9 ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X1 != X11
      | k3_tarski(k6_enumset1(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) != X9 ) ),
    inference(definition_unfolding,[],[f67,f92])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) ),
    inference(definition_unfolding,[],[f64,f90,f91])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X1 != X11
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
          & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
        & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f648,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(X2,sK1) )
    | ~ spl4_5 ),
    inference(superposition,[],[f125,f644])).

fof(f644,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f642])).

fof(f642,plain,
    ( spl4_5
  <=> sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f125,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f90])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f645,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f230,f225,f642])).

fof(f225,plain,
    ( spl4_4
  <=> r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f230,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f95,f227,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f227,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f225])).

fof(f95,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f90])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f228,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f223,f216,f225])).

fof(f216,plain,
    ( spl4_3
  <=> r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f223,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f222,f164])).

fof(f164,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[],[f96,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f96,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f47,f90,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f222,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f221,f43])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f221,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f220,f157])).

fof(f157,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f52,f43])).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f220,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f218,f96])).

fof(f218,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f216])).

fof(f219,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f94,f216])).

fof(f94,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f38,f90,f91])).

fof(f38,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f151,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f39,f148])).

fof(f39,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:23:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (21865)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (21857)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (21849)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (21860)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (21841)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (21854)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (21848)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (21847)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (21844)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.56  % (21845)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.56  % (21851)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (21856)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (21858)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (21851)Refutation not found, incomplete strategy% (21851)------------------------------
% 0.22/0.56  % (21851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (21851)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (21851)Memory used [KB]: 10874
% 0.22/0.56  % (21851)Time elapsed: 0.161 s
% 0.22/0.56  % (21851)------------------------------
% 0.22/0.56  % (21851)------------------------------
% 0.22/0.56  % (21862)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (21856)Refutation not found, incomplete strategy% (21856)------------------------------
% 0.22/0.56  % (21856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (21856)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (21856)Memory used [KB]: 1791
% 0.22/0.56  % (21856)Time elapsed: 0.146 s
% 0.22/0.56  % (21856)------------------------------
% 0.22/0.56  % (21856)------------------------------
% 0.22/0.57  % (21853)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (21858)Refutation not found, incomplete strategy% (21858)------------------------------
% 0.22/0.57  % (21858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (21858)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (21858)Memory used [KB]: 10746
% 0.22/0.57  % (21858)Time elapsed: 0.150 s
% 0.22/0.57  % (21858)------------------------------
% 0.22/0.57  % (21858)------------------------------
% 0.22/0.57  % (21846)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.52/0.57  % (21866)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.52/0.57  % (21863)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.52/0.57  % (21861)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.52/0.57  % (21843)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.52/0.57  % (21842)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.52/0.57  % (21842)Refutation not found, incomplete strategy% (21842)------------------------------
% 1.52/0.57  % (21842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (21842)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (21842)Memory used [KB]: 1663
% 1.52/0.57  % (21842)Time elapsed: 0.158 s
% 1.52/0.57  % (21842)------------------------------
% 1.52/0.57  % (21842)------------------------------
% 1.52/0.57  % (21859)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.52/0.57  % (21864)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.52/0.57  % (21870)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.52/0.58  % (21867)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.52/0.58  % (21855)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.52/0.58  % (21850)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.52/0.58  % (21870)Refutation not found, incomplete strategy% (21870)------------------------------
% 1.52/0.58  % (21870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.58  % (21869)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.52/0.58  % (21871)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.52/0.58  % (21871)Refutation not found, incomplete strategy% (21871)------------------------------
% 1.52/0.58  % (21871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.58  % (21871)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.58  
% 1.52/0.58  % (21871)Memory used [KB]: 1663
% 1.52/0.58  % (21871)Time elapsed: 0.001 s
% 1.52/0.58  % (21871)------------------------------
% 1.52/0.58  % (21871)------------------------------
% 1.70/0.59  % (21859)Refutation not found, incomplete strategy% (21859)------------------------------
% 1.70/0.59  % (21859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.60  % (21868)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.70/0.60  % (21868)Refutation not found, incomplete strategy% (21868)------------------------------
% 1.70/0.60  % (21868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.60  % (21870)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.60  
% 1.70/0.60  % (21870)Memory used [KB]: 10874
% 1.70/0.60  % (21870)Time elapsed: 0.173 s
% 1.70/0.60  % (21870)------------------------------
% 1.70/0.60  % (21870)------------------------------
% 1.70/0.60  % (21859)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.60  
% 1.70/0.60  % (21859)Memory used [KB]: 1918
% 1.70/0.60  % (21859)Time elapsed: 0.137 s
% 1.70/0.60  % (21859)------------------------------
% 1.70/0.60  % (21859)------------------------------
% 1.70/0.60  % (21868)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.60  
% 1.70/0.60  % (21868)Memory used [KB]: 6268
% 1.70/0.60  % (21868)Time elapsed: 0.156 s
% 1.70/0.60  % (21868)------------------------------
% 1.70/0.60  % (21868)------------------------------
% 2.14/0.68  % (21896)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.14/0.69  % (21844)Refutation not found, incomplete strategy% (21844)------------------------------
% 2.14/0.69  % (21844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.69  % (21844)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.69  
% 2.14/0.69  % (21844)Memory used [KB]: 6140
% 2.14/0.69  % (21844)Time elapsed: 0.281 s
% 2.14/0.69  % (21844)------------------------------
% 2.14/0.69  % (21844)------------------------------
% 2.14/0.70  % (21895)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.14/0.70  % (21899)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.14/0.70  % (21899)Refutation not found, incomplete strategy% (21899)------------------------------
% 2.14/0.70  % (21899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.70  % (21899)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.70  
% 2.14/0.70  % (21899)Memory used [KB]: 10746
% 2.14/0.70  % (21899)Time elapsed: 0.092 s
% 2.14/0.70  % (21899)------------------------------
% 2.14/0.70  % (21899)------------------------------
% 2.50/0.71  % (21898)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.50/0.72  % (21897)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.50/0.74  % (21903)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.50/0.74  % (21902)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.81/0.77  % (21862)Refutation found. Thanks to Tanya!
% 2.81/0.77  % SZS status Theorem for theBenchmark
% 2.81/0.77  % (21901)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.81/0.77  % SZS output start Proof for theBenchmark
% 2.81/0.77  fof(f741,plain,(
% 2.81/0.77    $false),
% 2.81/0.77    inference(avatar_sat_refutation,[],[f151,f219,f228,f645,f740])).
% 2.81/0.77  fof(f740,plain,(
% 2.81/0.77    spl4_1 | ~spl4_5),
% 2.81/0.77    inference(avatar_contradiction_clause,[],[f739])).
% 2.81/0.77  fof(f739,plain,(
% 2.81/0.77    $false | (spl4_1 | ~spl4_5)),
% 2.81/0.77    inference(subsumption_resolution,[],[f694,f150])).
% 2.81/0.77  fof(f150,plain,(
% 2.81/0.77    ~r2_hidden(sK0,sK1) | spl4_1),
% 2.81/0.77    inference(avatar_component_clause,[],[f148])).
% 2.81/0.77  fof(f148,plain,(
% 2.81/0.77    spl4_1 <=> r2_hidden(sK0,sK1)),
% 2.81/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.81/0.77  fof(f694,plain,(
% 2.81/0.77    r2_hidden(sK0,sK1) | ~spl4_5),
% 2.81/0.77    inference(resolution,[],[f648,f333])).
% 2.81/0.77  fof(f333,plain,(
% 2.81/0.77    ( ! [X61,X59,X57,X62,X60,X58,X56,X63] : (r2_hidden(X56,k6_enumset1(X56,X57,X58,X59,X60,X61,X62,X63))) )),
% 2.81/0.77    inference(superposition,[],[f143,f93])).
% 2.81/0.78  fof(f93,plain,(
% 2.81/0.78    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))) )),
% 2.81/0.78    inference(definition_unfolding,[],[f63,f90,f62,f91])).
% 2.81/0.79  fof(f91,plain,(
% 2.81/0.79    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.81/0.79    inference(definition_unfolding,[],[f40,f89])).
% 2.81/0.79  fof(f89,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.81/0.79    inference(definition_unfolding,[],[f45,f88])).
% 2.81/0.79  fof(f88,plain,(
% 2.81/0.79    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.81/0.79    inference(definition_unfolding,[],[f51,f87])).
% 2.81/0.79  fof(f87,plain,(
% 2.81/0.79    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.81/0.79    inference(definition_unfolding,[],[f59,f86])).
% 2.81/0.79  fof(f86,plain,(
% 2.81/0.79    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.81/0.79    inference(definition_unfolding,[],[f60,f85])).
% 2.81/0.79  fof(f85,plain,(
% 2.81/0.79    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.81/0.79    inference(definition_unfolding,[],[f61,f62])).
% 2.81/0.79  fof(f61,plain,(
% 2.81/0.79    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f17])).
% 2.81/0.79  fof(f17,axiom,(
% 2.81/0.79    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.81/0.79  fof(f60,plain,(
% 2.81/0.79    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f16])).
% 2.81/0.79  fof(f16,axiom,(
% 2.81/0.79    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.81/0.79  fof(f59,plain,(
% 2.81/0.79    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f15])).
% 2.81/0.79  fof(f15,axiom,(
% 2.81/0.79    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.81/0.79  fof(f51,plain,(
% 2.81/0.79    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f14])).
% 2.81/0.79  fof(f14,axiom,(
% 2.81/0.79    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.81/0.79  fof(f45,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f13])).
% 2.81/0.79  fof(f13,axiom,(
% 2.81/0.79    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.81/0.79  fof(f40,plain,(
% 2.81/0.79    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f12])).
% 2.81/0.79  fof(f12,axiom,(
% 2.81/0.79    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.81/0.79  fof(f62,plain,(
% 2.81/0.79    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f18])).
% 2.81/0.79  fof(f18,axiom,(
% 2.81/0.79    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.81/0.79  fof(f90,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.81/0.79    inference(definition_unfolding,[],[f44,f89])).
% 2.81/0.79  fof(f44,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.81/0.79    inference(cnf_transformation,[],[f19])).
% 2.81/0.79  fof(f19,axiom,(
% 2.81/0.79    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.81/0.79  fof(f63,plain,(
% 2.81/0.79    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 2.81/0.79    inference(cnf_transformation,[],[f11])).
% 2.81/0.79  fof(f11,axiom,(
% 2.81/0.79    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 2.81/0.79  fof(f143,plain,(
% 2.81/0.79    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X11] : (r2_hidden(X11,k3_tarski(k6_enumset1(k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))))) )),
% 2.81/0.79    inference(equality_resolution,[],[f142])).
% 2.81/0.79  fof(f142,plain,(
% 2.81/0.79    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X11,X9] : (r2_hidden(X11,X9) | k3_tarski(k6_enumset1(k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X11,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) != X9) )),
% 2.81/0.79    inference(equality_resolution,[],[f120])).
% 2.81/0.79  fof(f120,plain,(
% 2.81/0.79    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X1 != X11 | k3_tarski(k6_enumset1(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) != X9) )),
% 2.81/0.79    inference(definition_unfolding,[],[f67,f92])).
% 2.81/0.79  fof(f92,plain,(
% 2.81/0.79    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8)))) )),
% 2.81/0.79    inference(definition_unfolding,[],[f64,f90,f91])).
% 2.81/0.79  fof(f64,plain,(
% 2.81/0.79    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))) )),
% 2.81/0.79    inference(cnf_transformation,[],[f10])).
% 2.81/0.79  fof(f10,axiom,(
% 2.81/0.79    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).
% 2.81/0.79  fof(f67,plain,(
% 2.81/0.79    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X1 != X11 | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 2.81/0.79    inference(cnf_transformation,[],[f37])).
% 2.81/0.79  fof(f37,plain,(
% 2.81/0.79    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | (((sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 2.81/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 2.81/0.79  fof(f36,plain,(
% 2.81/0.79    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9))) => (((sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 2.81/0.79    introduced(choice_axiom,[])).
% 2.81/0.79  fof(f35,plain,(
% 2.81/0.79    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 2.81/0.79    inference(rectify,[],[f34])).
% 2.81/0.79  fof(f34,plain,(
% 2.81/0.79    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 2.81/0.79    inference(flattening,[],[f33])).
% 2.81/0.79  fof(f33,plain,(
% 2.81/0.79    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~r2_hidden(X10,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 2.81/0.79    inference(nnf_transformation,[],[f23])).
% 2.81/0.79  fof(f23,plain,(
% 2.81/0.79    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 2.81/0.79    inference(ennf_transformation,[],[f9])).
% 2.81/0.79  fof(f9,axiom,(
% 2.81/0.79    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).
% 2.81/0.79  fof(f648,plain,(
% 2.81/0.79    ( ! [X2] : (~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X2,sK1)) ) | ~spl4_5),
% 2.81/0.79    inference(superposition,[],[f125,f644])).
% 2.81/0.79  fof(f644,plain,(
% 2.81/0.79    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl4_5),
% 2.81/0.79    inference(avatar_component_clause,[],[f642])).
% 2.81/0.79  fof(f642,plain,(
% 2.81/0.79    spl4_5 <=> sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.81/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.81/0.79  fof(f125,plain,(
% 2.81/0.79    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.81/0.79    inference(equality_resolution,[],[f100])).
% 2.81/0.79  fof(f100,plain,(
% 2.81/0.79    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.81/0.79    inference(definition_unfolding,[],[f55,f90])).
% 2.81/0.79  fof(f55,plain,(
% 2.81/0.79    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.81/0.79    inference(cnf_transformation,[],[f32])).
% 2.81/0.79  fof(f32,plain,(
% 2.81/0.79    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.81/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 2.81/0.79  fof(f31,plain,(
% 2.81/0.79    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.81/0.79    introduced(choice_axiom,[])).
% 2.81/0.79  fof(f30,plain,(
% 2.81/0.79    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.81/0.79    inference(rectify,[],[f29])).
% 2.81/0.79  fof(f29,plain,(
% 2.81/0.79    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.81/0.79    inference(flattening,[],[f28])).
% 2.81/0.79  fof(f28,plain,(
% 2.81/0.79    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.81/0.79    inference(nnf_transformation,[],[f3])).
% 2.81/0.79  fof(f3,axiom,(
% 2.81/0.79    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.81/0.79  fof(f645,plain,(
% 2.81/0.79    spl4_5 | ~spl4_4),
% 2.81/0.79    inference(avatar_split_clause,[],[f230,f225,f642])).
% 2.81/0.79  fof(f225,plain,(
% 2.81/0.79    spl4_4 <=> r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.81/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.81/0.79  fof(f230,plain,(
% 2.81/0.79    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl4_4),
% 2.81/0.79    inference(unit_resulting_resolution,[],[f95,f227,f50])).
% 2.81/0.79  fof(f50,plain,(
% 2.81/0.79    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f27])).
% 2.81/0.79  fof(f27,plain,(
% 2.81/0.79    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.81/0.79    inference(flattening,[],[f26])).
% 2.81/0.79  fof(f26,plain,(
% 2.81/0.79    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.81/0.79    inference(nnf_transformation,[],[f4])).
% 2.81/0.79  fof(f4,axiom,(
% 2.81/0.79    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.81/0.79  fof(f227,plain,(
% 2.81/0.79    r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~spl4_4),
% 2.81/0.79    inference(avatar_component_clause,[],[f225])).
% 2.81/0.79  fof(f95,plain,(
% 2.81/0.79    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.81/0.79    inference(definition_unfolding,[],[f41,f90])).
% 2.81/0.79  fof(f41,plain,(
% 2.81/0.79    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.81/0.79    inference(cnf_transformation,[],[f6])).
% 2.81/0.79  fof(f6,axiom,(
% 2.81/0.79    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.81/0.79  fof(f228,plain,(
% 2.81/0.79    spl4_4 | ~spl4_3),
% 2.81/0.79    inference(avatar_split_clause,[],[f223,f216,f225])).
% 2.81/0.79  fof(f216,plain,(
% 2.81/0.79    spl4_3 <=> r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 2.81/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.81/0.79  fof(f223,plain,(
% 2.81/0.79    r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~spl4_3),
% 2.81/0.79    inference(forward_demodulation,[],[f222,f164])).
% 2.81/0.79  fof(f164,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) )),
% 2.81/0.79    inference(superposition,[],[f96,f42])).
% 2.81/0.79  fof(f42,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f1])).
% 2.81/0.79  fof(f1,axiom,(
% 2.81/0.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.81/0.79  fof(f96,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.81/0.79    inference(definition_unfolding,[],[f47,f90,f46])).
% 2.81/0.79  fof(f46,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.81/0.79    inference(cnf_transformation,[],[f5])).
% 2.81/0.79  fof(f5,axiom,(
% 2.81/0.79    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.81/0.79  fof(f47,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.81/0.79    inference(cnf_transformation,[],[f8])).
% 2.81/0.79  fof(f8,axiom,(
% 2.81/0.79    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.81/0.79  fof(f222,plain,(
% 2.81/0.79    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) | ~spl4_3),
% 2.81/0.79    inference(forward_demodulation,[],[f221,f43])).
% 2.81/0.79  fof(f43,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f2])).
% 2.81/0.79  fof(f2,axiom,(
% 2.81/0.79    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.81/0.79  fof(f221,plain,(
% 2.81/0.79    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~spl4_3),
% 2.81/0.79    inference(forward_demodulation,[],[f220,f157])).
% 2.81/0.79  fof(f157,plain,(
% 2.81/0.79    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 2.81/0.79    inference(superposition,[],[f52,f43])).
% 2.81/0.79  fof(f52,plain,(
% 2.81/0.79    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.81/0.79    inference(cnf_transformation,[],[f7])).
% 2.81/0.79  fof(f7,axiom,(
% 2.81/0.79    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.81/0.79  fof(f220,plain,(
% 2.81/0.79    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) | ~spl4_3),
% 2.81/0.79    inference(forward_demodulation,[],[f218,f96])).
% 2.81/0.79  fof(f218,plain,(
% 2.81/0.79    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) | ~spl4_3),
% 2.81/0.79    inference(avatar_component_clause,[],[f216])).
% 2.81/0.79  fof(f219,plain,(
% 2.81/0.79    spl4_3),
% 2.81/0.79    inference(avatar_split_clause,[],[f94,f216])).
% 2.81/0.79  fof(f94,plain,(
% 2.81/0.79    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 2.81/0.79    inference(definition_unfolding,[],[f38,f90,f91])).
% 2.81/0.79  fof(f38,plain,(
% 2.81/0.79    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.81/0.79    inference(cnf_transformation,[],[f25])).
% 2.81/0.79  fof(f25,plain,(
% 2.81/0.79    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.81/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24])).
% 2.81/0.79  fof(f24,plain,(
% 2.81/0.79    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 2.81/0.79    introduced(choice_axiom,[])).
% 2.81/0.79  fof(f22,plain,(
% 2.81/0.79    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 2.81/0.79    inference(ennf_transformation,[],[f21])).
% 2.81/0.79  fof(f21,negated_conjecture,(
% 2.81/0.79    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.81/0.79    inference(negated_conjecture,[],[f20])).
% 2.81/0.79  fof(f20,conjecture,(
% 2.81/0.79    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.81/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 2.81/0.79  fof(f151,plain,(
% 2.81/0.79    ~spl4_1),
% 2.81/0.79    inference(avatar_split_clause,[],[f39,f148])).
% 2.81/0.79  fof(f39,plain,(
% 2.81/0.79    ~r2_hidden(sK0,sK1)),
% 2.81/0.79    inference(cnf_transformation,[],[f25])).
% 2.81/0.79  % SZS output end Proof for theBenchmark
% 2.81/0.79  % (21862)------------------------------
% 2.81/0.79  % (21862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.79  % (21862)Termination reason: Refutation
% 2.81/0.79  
% 2.81/0.79  % (21862)Memory used [KB]: 12792
% 2.81/0.79  % (21862)Time elapsed: 0.352 s
% 2.81/0.79  % (21862)------------------------------
% 2.81/0.79  % (21862)------------------------------
% 2.81/0.79  % (21834)Success in time 0.419 s
%------------------------------------------------------------------------------
