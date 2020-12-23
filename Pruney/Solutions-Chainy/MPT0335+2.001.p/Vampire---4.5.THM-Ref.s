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
% DateTime   : Thu Dec  3 12:43:15 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 737 expanded)
%              Number of leaves         :   25 ( 226 expanded)
%              Depth                    :   21
%              Number of atoms          :  408 (2162 expanded)
%              Number of equality atoms :  190 (1023 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2954,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f175,f431,f507,f517,f2949])).

fof(f2949,plain,(
    ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f2948])).

fof(f2948,plain,
    ( $false
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f2947,f2150])).

fof(f2150,plain,(
    sK0 != k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f2133,f46])).

fof(f46,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f2133,plain,
    ( sK0 != k4_xboole_0(sK0,sK2)
    | ~ r2_hidden(sK3,sK0) ),
    inference(superposition,[],[f139,f1964])).

fof(f1964,plain,(
    ! [X2] : k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X2))) ),
    inference(forward_demodulation,[],[f1942,f93])).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1942,plain,(
    ! [X2] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X2))) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X2))) ),
    inference(superposition,[],[f93,f176])).

fof(f176,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f96,f134])).

fof(f134,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f92,f121])).

fof(f121,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f44,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f44,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f96,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f67,f55,f55,f55,f55])).

fof(f67,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f139,plain,(
    ! [X6] :
      ( k4_xboole_0(X6,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != X6
      | ~ r2_hidden(sK3,X6) ) ),
    inference(superposition,[],[f95,f88])).

fof(f88,plain,(
    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f45,f86,f55])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f64,f86])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f2947,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f2931,f1568])).

fof(f1568,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f89,f1567])).

fof(f1567,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1566,f522])).

fof(f522,plain,
    ( ! [X3] : ~ r2_hidden(X3,k1_xboole_0)
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f188,f430])).

fof(f430,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl6_24
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f188,plain,(
    ! [X3] : ~ r2_hidden(X3,k4_xboole_0(sK0,sK0)) ),
    inference(forward_demodulation,[],[f187,f177])).

fof(f177,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f93,f134])).

fof(f187,plain,(
    ! [X3] : ~ r2_hidden(X3,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f183,f110])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f183,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(X3,k4_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f109,f134])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1566,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X0)
        | r2_hidden(sK5(X0,X0,k1_xboole_0),k1_xboole_0) )
    | ~ spl6_24 ),
    inference(duplicate_literal_removal,[],[f1555])).

fof(f1555,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X0)
        | k1_xboole_0 = k4_xboole_0(X0,X0)
        | r2_hidden(sK5(X0,X0,k1_xboole_0),k1_xboole_0) )
    | ~ spl6_24 ),
    inference(resolution,[],[f534,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f534,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK5(X2,X3,k1_xboole_0),X2)
        | k1_xboole_0 = k4_xboole_0(X2,X3) )
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f527,f430])).

fof(f527,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK5(X2,X3,k1_xboole_0),X2)
        | k4_xboole_0(sK0,sK0) = k4_xboole_0(X2,X3) )
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f203,f430])).

fof(f203,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3,k4_xboole_0(sK0,sK0)),X2)
      | k4_xboole_0(sK0,sK0) = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f188,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f49,f55])).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f2931,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f93,f2923])).

fof(f2923,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f2887,f135])).

fof(f135,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f87,f88])).

fof(f87,plain,(
    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f47,f86,f55])).

fof(f47,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f2887,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f872,f1964])).

fof(f872,plain,(
    ! [X2] :
      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
      | k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ) ),
    inference(superposition,[],[f249,f91])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f51,f55,f55])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f249,plain,(
    ! [X0] :
      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))
      | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) ) ),
    inference(resolution,[],[f152,f90])).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f152,plain,(
    ! [X10] :
      ( ~ r1_tarski(X10,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10
      | k1_xboole_0 = X10 ) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X10] :
      ( ~ r1_tarski(X10,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10
      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10
      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10
      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10
      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10
      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10
      | k1_xboole_0 = X10
      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10 ) ),
    inference(superposition,[],[f105,f88])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k3_enumset1(X0,X0,X0,X1,X2))
      | k3_enumset1(X0,X0,X0,X0,X2) = X3
      | k3_enumset1(X1,X1,X1,X1,X2) = X3
      | k3_enumset1(X0,X0,X0,X0,X1) = X3
      | k3_enumset1(X2,X2,X2,X2,X2) = X3
      | k3_enumset1(X1,X1,X1,X1,X1) = X3
      | k3_enumset1(X0,X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | k3_enumset1(X0,X0,X0,X1,X2) = X3 ) ),
    inference(definition_unfolding,[],[f75,f84,f85,f85,f85,f86,f86,f86,f84])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f517,plain,
    ( ~ spl6_4
    | ~ spl6_23
    | spl6_24 ),
    inference(avatar_contradiction_clause,[],[f516])).

fof(f516,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_23
    | spl6_24 ),
    inference(subsumption_resolution,[],[f515,f429])).

fof(f429,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f428])).

fof(f515,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f426,f174])).

fof(f174,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl6_4
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f426,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK0)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl6_23
  <=> k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f507,plain,
    ( spl6_3
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | spl6_3
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f459,f188])).

fof(f459,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK0),k1_xboole_0),k4_xboole_0(sK0,sK0))
    | spl6_3
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f211,f426])).

fof(f211,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl6_3 ),
    inference(resolution,[],[f170,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f170,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_3
  <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f431,plain,
    ( spl6_23
    | spl6_24 ),
    inference(avatar_split_clause,[],[f421,f428,f424])).

fof(f421,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f252,f188])).

fof(f252,plain,(
    ! [X1] :
      ( r2_hidden(sK4(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X1)
      | k1_xboole_0 = X1
      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X1 ) ),
    inference(resolution,[],[f152,f62])).

fof(f175,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f165,f172,f168])).

fof(f165,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
    inference(resolution,[],[f151,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f151,plain,(
    r1_tarski(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f118,f88])).

fof(f118,plain,(
    ! [X2,X0,X1] : r1_tarski(k1_xboole_0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k3_enumset1(X0,X0,X0,X1,X2))
      | k1_xboole_0 != X3 ) ),
    inference(definition_unfolding,[],[f76,f84])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k1_xboole_0 != X3 ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (29462)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (29475)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (29488)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (29463)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (29470)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (29459)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (29480)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (29466)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (29469)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (29468)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (29482)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (29460)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (29461)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (29474)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (29464)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (29483)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (29487)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (29473)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (29477)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (29486)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (29476)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (29467)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (29479)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.56  % (29481)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.56  % (29471)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (29478)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.57  % (29484)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.57  % (29465)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.58  % (29485)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.58  % (29472)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.70/0.77  % (29467)Refutation found. Thanks to Tanya!
% 2.70/0.77  % SZS status Theorem for theBenchmark
% 2.70/0.78  % SZS output start Proof for theBenchmark
% 2.70/0.78  fof(f2954,plain,(
% 2.70/0.78    $false),
% 2.70/0.78    inference(avatar_sat_refutation,[],[f175,f431,f507,f517,f2949])).
% 2.70/0.78  fof(f2949,plain,(
% 2.70/0.78    ~spl6_24),
% 2.70/0.78    inference(avatar_contradiction_clause,[],[f2948])).
% 2.70/0.78  fof(f2948,plain,(
% 2.70/0.78    $false | ~spl6_24),
% 2.70/0.78    inference(subsumption_resolution,[],[f2947,f2150])).
% 2.70/0.78  fof(f2150,plain,(
% 2.70/0.78    sK0 != k4_xboole_0(sK0,sK2)),
% 2.70/0.78    inference(subsumption_resolution,[],[f2133,f46])).
% 2.70/0.78  fof(f46,plain,(
% 2.70/0.78    r2_hidden(sK3,sK0)),
% 2.70/0.78    inference(cnf_transformation,[],[f29])).
% 2.70/0.78  fof(f29,plain,(
% 2.70/0.78    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 2.70/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f28])).
% 2.70/0.78  fof(f28,plain,(
% 2.70/0.78    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 2.70/0.78    introduced(choice_axiom,[])).
% 2.70/0.78  fof(f23,plain,(
% 2.70/0.78    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 2.70/0.78    inference(flattening,[],[f22])).
% 2.70/0.78  fof(f22,plain,(
% 2.70/0.78    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 2.70/0.78    inference(ennf_transformation,[],[f20])).
% 2.70/0.78  fof(f20,negated_conjecture,(
% 2.70/0.78    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 2.70/0.78    inference(negated_conjecture,[],[f19])).
% 2.70/0.78  fof(f19,conjecture,(
% 2.70/0.78    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 2.70/0.78  fof(f2133,plain,(
% 2.70/0.78    sK0 != k4_xboole_0(sK0,sK2) | ~r2_hidden(sK3,sK0)),
% 2.70/0.78    inference(superposition,[],[f139,f1964])).
% 2.70/0.78  fof(f1964,plain,(
% 2.70/0.78    ( ! [X2] : (k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X2)))) )),
% 2.70/0.78    inference(forward_demodulation,[],[f1942,f93])).
% 2.70/0.78  fof(f93,plain,(
% 2.70/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.70/0.78    inference(definition_unfolding,[],[f54,f55])).
% 2.70/0.78  fof(f55,plain,(
% 2.70/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.70/0.78    inference(cnf_transformation,[],[f12])).
% 2.70/0.78  fof(f12,axiom,(
% 2.70/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.70/0.78  fof(f54,plain,(
% 2.70/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.70/0.78    inference(cnf_transformation,[],[f11])).
% 2.70/0.78  fof(f11,axiom,(
% 2.70/0.78    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.70/0.78  fof(f1942,plain,(
% 2.70/0.78    ( ! [X2] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X2))) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X2)))) )),
% 2.70/0.78    inference(superposition,[],[f93,f176])).
% 2.70/0.78  fof(f176,plain,(
% 2.70/0.78    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) )),
% 2.70/0.78    inference(superposition,[],[f96,f134])).
% 2.70/0.78  fof(f134,plain,(
% 2.70/0.78    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.70/0.78    inference(superposition,[],[f92,f121])).
% 2.70/0.78  fof(f121,plain,(
% 2.70/0.78    sK1 = k2_xboole_0(sK0,sK1)),
% 2.70/0.78    inference(resolution,[],[f44,f57])).
% 2.70/0.78  fof(f57,plain,(
% 2.70/0.78    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.70/0.78    inference(cnf_transformation,[],[f25])).
% 2.70/0.78  fof(f25,plain,(
% 2.70/0.78    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.70/0.78    inference(ennf_transformation,[],[f7])).
% 2.70/0.78  fof(f7,axiom,(
% 2.70/0.78    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.70/0.78  fof(f44,plain,(
% 2.70/0.78    r1_tarski(sK0,sK1)),
% 2.70/0.78    inference(cnf_transformation,[],[f29])).
% 2.70/0.78  fof(f92,plain,(
% 2.70/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 2.70/0.78    inference(definition_unfolding,[],[f52,f55])).
% 2.70/0.78  fof(f52,plain,(
% 2.70/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.70/0.78    inference(cnf_transformation,[],[f10])).
% 2.70/0.78  fof(f10,axiom,(
% 2.70/0.78    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.70/0.78  fof(f96,plain,(
% 2.70/0.78    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 2.70/0.78    inference(definition_unfolding,[],[f67,f55,f55,f55,f55])).
% 2.70/0.78  fof(f67,plain,(
% 2.70/0.78    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 2.70/0.78    inference(cnf_transformation,[],[f8])).
% 2.70/0.78  fof(f8,axiom,(
% 2.70/0.78    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 2.70/0.78  fof(f139,plain,(
% 2.70/0.78    ( ! [X6] : (k4_xboole_0(X6,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != X6 | ~r2_hidden(sK3,X6)) )),
% 2.70/0.78    inference(superposition,[],[f95,f88])).
% 2.70/0.78  fof(f88,plain,(
% 2.70/0.78    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.70/0.78    inference(definition_unfolding,[],[f45,f86,f55])).
% 2.70/0.78  fof(f86,plain,(
% 2.70/0.78    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.70/0.78    inference(definition_unfolding,[],[f48,f85])).
% 2.70/0.78  fof(f85,plain,(
% 2.70/0.78    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.70/0.78    inference(definition_unfolding,[],[f53,f84])).
% 2.70/0.78  fof(f84,plain,(
% 2.70/0.78    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.70/0.78    inference(definition_unfolding,[],[f66,f74])).
% 2.70/0.78  fof(f74,plain,(
% 2.70/0.78    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.70/0.78    inference(cnf_transformation,[],[f16])).
% 2.70/0.78  fof(f16,axiom,(
% 2.70/0.78    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.70/0.78  fof(f66,plain,(
% 2.70/0.78    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.70/0.78    inference(cnf_transformation,[],[f15])).
% 2.70/0.78  fof(f15,axiom,(
% 2.70/0.78    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.70/0.78  fof(f53,plain,(
% 2.70/0.78    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.70/0.78    inference(cnf_transformation,[],[f14])).
% 2.70/0.78  fof(f14,axiom,(
% 2.70/0.78    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.70/0.78  fof(f48,plain,(
% 2.70/0.78    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.70/0.78    inference(cnf_transformation,[],[f13])).
% 2.70/0.78  fof(f13,axiom,(
% 2.70/0.78    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.70/0.78  fof(f45,plain,(
% 2.70/0.78    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 2.70/0.78    inference(cnf_transformation,[],[f29])).
% 2.70/0.78  fof(f95,plain,(
% 2.70/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 2.70/0.78    inference(definition_unfolding,[],[f64,f86])).
% 2.70/0.78  fof(f64,plain,(
% 2.70/0.78    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 2.70/0.78    inference(cnf_transformation,[],[f36])).
% 2.70/0.78  fof(f36,plain,(
% 2.70/0.78    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.70/0.78    inference(nnf_transformation,[],[f18])).
% 2.70/0.78  fof(f18,axiom,(
% 2.70/0.78    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 2.70/0.78  fof(f2947,plain,(
% 2.70/0.78    sK0 = k4_xboole_0(sK0,sK2) | ~spl6_24),
% 2.70/0.78    inference(forward_demodulation,[],[f2931,f1568])).
% 2.70/0.78  fof(f1568,plain,(
% 2.70/0.78    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl6_24),
% 2.70/0.78    inference(backward_demodulation,[],[f89,f1567])).
% 2.70/0.78  fof(f1567,plain,(
% 2.70/0.78    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl6_24),
% 2.70/0.78    inference(subsumption_resolution,[],[f1566,f522])).
% 2.70/0.78  fof(f522,plain,(
% 2.70/0.78    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) ) | ~spl6_24),
% 2.70/0.78    inference(backward_demodulation,[],[f188,f430])).
% 2.70/0.78  fof(f430,plain,(
% 2.70/0.78    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl6_24),
% 2.70/0.78    inference(avatar_component_clause,[],[f428])).
% 2.70/0.78  fof(f428,plain,(
% 2.70/0.78    spl6_24 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 2.70/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 2.70/0.78  fof(f188,plain,(
% 2.70/0.78    ( ! [X3] : (~r2_hidden(X3,k4_xboole_0(sK0,sK0))) )),
% 2.70/0.78    inference(forward_demodulation,[],[f187,f177])).
% 2.70/0.78  fof(f177,plain,(
% 2.70/0.78    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0)),
% 2.70/0.78    inference(superposition,[],[f93,f134])).
% 2.70/0.78  fof(f187,plain,(
% 2.70/0.78    ( ! [X3] : (~r2_hidden(X3,k4_xboole_0(sK0,sK1))) )),
% 2.70/0.78    inference(subsumption_resolution,[],[f183,f110])).
% 2.70/0.78  fof(f110,plain,(
% 2.70/0.78    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 2.70/0.78    inference(equality_resolution,[],[f68])).
% 2.70/0.78  fof(f68,plain,(
% 2.70/0.78    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.70/0.78    inference(cnf_transformation,[],[f41])).
% 2.70/0.78  fof(f41,plain,(
% 2.70/0.78    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.70/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 2.70/0.78  fof(f40,plain,(
% 2.70/0.78    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.70/0.78    introduced(choice_axiom,[])).
% 2.70/0.78  fof(f39,plain,(
% 2.70/0.78    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.70/0.78    inference(rectify,[],[f38])).
% 2.70/0.78  fof(f38,plain,(
% 2.70/0.78    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.70/0.78    inference(flattening,[],[f37])).
% 2.70/0.78  fof(f37,plain,(
% 2.70/0.78    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.70/0.78    inference(nnf_transformation,[],[f4])).
% 2.70/0.78  fof(f4,axiom,(
% 2.70/0.78    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.70/0.78  fof(f183,plain,(
% 2.70/0.78    ( ! [X3] : (~r2_hidden(X3,sK0) | ~r2_hidden(X3,k4_xboole_0(sK0,sK1))) )),
% 2.70/0.78    inference(superposition,[],[f109,f134])).
% 2.70/0.78  fof(f109,plain,(
% 2.70/0.78    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.70/0.78    inference(equality_resolution,[],[f69])).
% 2.70/0.78  fof(f69,plain,(
% 2.70/0.78    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.70/0.78    inference(cnf_transformation,[],[f41])).
% 2.70/0.78  fof(f1566,plain,(
% 2.70/0.78    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | r2_hidden(sK5(X0,X0,k1_xboole_0),k1_xboole_0)) ) | ~spl6_24),
% 2.70/0.78    inference(duplicate_literal_removal,[],[f1555])).
% 2.70/0.78  fof(f1555,plain,(
% 2.70/0.78    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0) | r2_hidden(sK5(X0,X0,k1_xboole_0),k1_xboole_0)) ) | ~spl6_24),
% 2.70/0.78    inference(resolution,[],[f534,f72])).
% 2.70/0.78  fof(f72,plain,(
% 2.70/0.78    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.70/0.78    inference(cnf_transformation,[],[f41])).
% 2.70/0.78  fof(f534,plain,(
% 2.70/0.78    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3,k1_xboole_0),X2) | k1_xboole_0 = k4_xboole_0(X2,X3)) ) | ~spl6_24),
% 2.70/0.78    inference(forward_demodulation,[],[f527,f430])).
% 2.70/0.78  fof(f527,plain,(
% 2.70/0.78    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3,k1_xboole_0),X2) | k4_xboole_0(sK0,sK0) = k4_xboole_0(X2,X3)) ) | ~spl6_24),
% 2.70/0.78    inference(backward_demodulation,[],[f203,f430])).
% 2.70/0.78  fof(f203,plain,(
% 2.70/0.78    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3,k4_xboole_0(sK0,sK0)),X2) | k4_xboole_0(sK0,sK0) = k4_xboole_0(X2,X3)) )),
% 2.70/0.78    inference(resolution,[],[f188,f71])).
% 2.70/0.78  fof(f71,plain,(
% 2.70/0.78    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.70/0.78    inference(cnf_transformation,[],[f41])).
% 2.70/0.78  fof(f89,plain,(
% 2.70/0.78    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.70/0.78    inference(definition_unfolding,[],[f49,f55])).
% 2.70/0.78  fof(f49,plain,(
% 2.70/0.78    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.70/0.78    inference(cnf_transformation,[],[f21])).
% 2.70/0.78  fof(f21,plain,(
% 2.70/0.78    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.70/0.78    inference(rectify,[],[f5])).
% 2.70/0.78  fof(f5,axiom,(
% 2.70/0.78    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.70/0.78  fof(f2931,plain,(
% 2.70/0.78    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 2.70/0.78    inference(superposition,[],[f93,f2923])).
% 2.70/0.78  fof(f2923,plain,(
% 2.70/0.78    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.70/0.78    inference(subsumption_resolution,[],[f2887,f135])).
% 2.70/0.78  fof(f135,plain,(
% 2.70/0.78    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.70/0.78    inference(superposition,[],[f87,f88])).
% 2.70/0.78  fof(f87,plain,(
% 2.70/0.78    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.70/0.78    inference(definition_unfolding,[],[f47,f86,f55])).
% 2.70/0.78  fof(f47,plain,(
% 2.70/0.78    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 2.70/0.78    inference(cnf_transformation,[],[f29])).
% 2.70/0.78  fof(f2887,plain,(
% 2.70/0.78    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.70/0.78    inference(superposition,[],[f872,f1964])).
% 2.70/0.78  fof(f872,plain,(
% 2.70/0.78    ( ! [X2] : (k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) )),
% 2.70/0.78    inference(superposition,[],[f249,f91])).
% 2.70/0.78  fof(f91,plain,(
% 2.70/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.70/0.78    inference(definition_unfolding,[],[f51,f55,f55])).
% 2.70/0.78  fof(f51,plain,(
% 2.70/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.70/0.78    inference(cnf_transformation,[],[f2])).
% 2.70/0.78  fof(f2,axiom,(
% 2.70/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.70/0.78  fof(f249,plain,(
% 2.70/0.78    ( ! [X0] : (k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))) )),
% 2.70/0.78    inference(resolution,[],[f152,f90])).
% 2.70/0.78  fof(f90,plain,(
% 2.70/0.78    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.70/0.78    inference(definition_unfolding,[],[f50,f55])).
% 2.70/0.78  fof(f50,plain,(
% 2.70/0.78    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.70/0.78    inference(cnf_transformation,[],[f9])).
% 2.70/0.78  fof(f9,axiom,(
% 2.70/0.78    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.70/0.78  fof(f152,plain,(
% 2.70/0.78    ( ! [X10] : (~r1_tarski(X10,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10 | k1_xboole_0 = X10) )),
% 2.70/0.78    inference(duplicate_literal_removal,[],[f143])).
% 2.70/0.78  fof(f143,plain,(
% 2.70/0.78    ( ! [X10] : (~r1_tarski(X10,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10 | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10 | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10 | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10 | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10 | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10 | k1_xboole_0 = X10 | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X10) )),
% 2.70/0.78    inference(superposition,[],[f105,f88])).
% 2.70/0.78  fof(f105,plain,(
% 2.70/0.78    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k3_enumset1(X0,X0,X0,X1,X2)) | k3_enumset1(X0,X0,X0,X0,X2) = X3 | k3_enumset1(X1,X1,X1,X1,X2) = X3 | k3_enumset1(X0,X0,X0,X0,X1) = X3 | k3_enumset1(X2,X2,X2,X2,X2) = X3 | k3_enumset1(X1,X1,X1,X1,X1) = X3 | k3_enumset1(X0,X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | k3_enumset1(X0,X0,X0,X1,X2) = X3) )),
% 2.70/0.78    inference(definition_unfolding,[],[f75,f84,f85,f85,f85,f86,f86,f86,f84])).
% 2.70/0.78  fof(f75,plain,(
% 2.70/0.78    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 2.70/0.78    inference(cnf_transformation,[],[f43])).
% 2.70/0.78  fof(f43,plain,(
% 2.70/0.78    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.70/0.78    inference(flattening,[],[f42])).
% 2.70/0.78  fof(f42,plain,(
% 2.70/0.78    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.70/0.78    inference(nnf_transformation,[],[f27])).
% 2.70/0.78  fof(f27,plain,(
% 2.70/0.78    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.70/0.78    inference(ennf_transformation,[],[f17])).
% 2.70/0.78  fof(f17,axiom,(
% 2.70/0.78    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 2.70/0.78  fof(f517,plain,(
% 2.70/0.78    ~spl6_4 | ~spl6_23 | spl6_24),
% 2.70/0.78    inference(avatar_contradiction_clause,[],[f516])).
% 2.70/0.78  fof(f516,plain,(
% 2.70/0.78    $false | (~spl6_4 | ~spl6_23 | spl6_24)),
% 2.70/0.78    inference(subsumption_resolution,[],[f515,f429])).
% 2.70/0.78  fof(f429,plain,(
% 2.70/0.78    k1_xboole_0 != k4_xboole_0(sK0,sK0) | spl6_24),
% 2.70/0.78    inference(avatar_component_clause,[],[f428])).
% 2.70/0.78  fof(f515,plain,(
% 2.70/0.78    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl6_4 | ~spl6_23)),
% 2.70/0.78    inference(backward_demodulation,[],[f426,f174])).
% 2.70/0.78  fof(f174,plain,(
% 2.70/0.78    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl6_4),
% 2.70/0.78    inference(avatar_component_clause,[],[f172])).
% 2.70/0.78  fof(f172,plain,(
% 2.70/0.78    spl6_4 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.70/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.70/0.78  fof(f426,plain,(
% 2.70/0.78    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK0) | ~spl6_23),
% 2.70/0.78    inference(avatar_component_clause,[],[f424])).
% 2.70/0.78  fof(f424,plain,(
% 2.70/0.78    spl6_23 <=> k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK0)),
% 2.70/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 2.70/0.78  fof(f507,plain,(
% 2.70/0.78    spl6_3 | ~spl6_23),
% 2.70/0.78    inference(avatar_contradiction_clause,[],[f506])).
% 2.70/0.78  fof(f506,plain,(
% 2.70/0.78    $false | (spl6_3 | ~spl6_23)),
% 2.70/0.78    inference(subsumption_resolution,[],[f459,f188])).
% 2.70/0.78  fof(f459,plain,(
% 2.70/0.78    r2_hidden(sK4(k4_xboole_0(sK0,sK0),k1_xboole_0),k4_xboole_0(sK0,sK0)) | (spl6_3 | ~spl6_23)),
% 2.70/0.78    inference(backward_demodulation,[],[f211,f426])).
% 2.70/0.78  fof(f211,plain,(
% 2.70/0.78    r2_hidden(sK4(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl6_3),
% 2.70/0.78    inference(resolution,[],[f170,f62])).
% 2.70/0.78  fof(f62,plain,(
% 2.70/0.78    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 2.70/0.78    inference(cnf_transformation,[],[f35])).
% 2.70/0.78  fof(f35,plain,(
% 2.70/0.78    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.70/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 2.70/0.78  fof(f34,plain,(
% 2.70/0.78    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.70/0.78    introduced(choice_axiom,[])).
% 2.70/0.78  fof(f33,plain,(
% 2.70/0.78    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.70/0.78    inference(rectify,[],[f32])).
% 2.70/0.78  fof(f32,plain,(
% 2.70/0.78    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.70/0.78    inference(nnf_transformation,[],[f26])).
% 2.70/0.78  fof(f26,plain,(
% 2.70/0.78    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.70/0.78    inference(ennf_transformation,[],[f3])).
% 2.70/0.78  fof(f3,axiom,(
% 2.70/0.78    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.70/0.78  fof(f170,plain,(
% 2.70/0.78    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) | spl6_3),
% 2.70/0.78    inference(avatar_component_clause,[],[f168])).
% 2.70/0.78  fof(f168,plain,(
% 2.70/0.78    spl6_3 <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0)),
% 2.70/0.78    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.70/0.78  fof(f431,plain,(
% 2.70/0.78    spl6_23 | spl6_24),
% 2.70/0.78    inference(avatar_split_clause,[],[f421,f428,f424])).
% 2.70/0.78  fof(f421,plain,(
% 2.70/0.78    k1_xboole_0 = k4_xboole_0(sK0,sK0) | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK0)),
% 2.70/0.78    inference(resolution,[],[f252,f188])).
% 2.70/0.78  fof(f252,plain,(
% 2.70/0.78    ( ! [X1] : (r2_hidden(sK4(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X1) | k1_xboole_0 = X1 | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = X1) )),
% 2.70/0.78    inference(resolution,[],[f152,f62])).
% 2.70/0.78  fof(f175,plain,(
% 2.70/0.78    ~spl6_3 | spl6_4),
% 2.70/0.78    inference(avatar_split_clause,[],[f165,f172,f168])).
% 2.70/0.78  fof(f165,plain,(
% 2.70/0.78    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0)),
% 2.70/0.78    inference(resolution,[],[f151,f60])).
% 2.70/0.78  fof(f60,plain,(
% 2.70/0.78    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.70/0.78    inference(cnf_transformation,[],[f31])).
% 2.70/0.78  fof(f31,plain,(
% 2.70/0.78    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.70/0.78    inference(flattening,[],[f30])).
% 2.70/0.78  fof(f30,plain,(
% 2.70/0.78    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.70/0.78    inference(nnf_transformation,[],[f6])).
% 2.70/0.78  fof(f6,axiom,(
% 2.70/0.78    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.70/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.70/0.78  fof(f151,plain,(
% 2.70/0.78    r1_tarski(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 2.70/0.78    inference(superposition,[],[f118,f88])).
% 2.70/0.78  fof(f118,plain,(
% 2.70/0.78    ( ! [X2,X0,X1] : (r1_tarski(k1_xboole_0,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 2.70/0.78    inference(equality_resolution,[],[f104])).
% 2.70/0.78  fof(f104,plain,(
% 2.70/0.78    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k3_enumset1(X0,X0,X0,X1,X2)) | k1_xboole_0 != X3) )),
% 2.70/0.78    inference(definition_unfolding,[],[f76,f84])).
% 2.70/0.78  fof(f76,plain,(
% 2.70/0.78    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k1_xboole_0 != X3) )),
% 2.70/0.78    inference(cnf_transformation,[],[f43])).
% 2.70/0.78  % SZS output end Proof for theBenchmark
% 2.70/0.78  % (29467)------------------------------
% 2.70/0.78  % (29467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.78  % (29467)Termination reason: Refutation
% 2.70/0.78  
% 2.70/0.78  % (29467)Memory used [KB]: 12920
% 2.70/0.78  % (29467)Time elapsed: 0.327 s
% 2.70/0.78  % (29467)------------------------------
% 2.70/0.78  % (29467)------------------------------
% 2.70/0.78  % (29458)Success in time 0.416 s
%------------------------------------------------------------------------------
