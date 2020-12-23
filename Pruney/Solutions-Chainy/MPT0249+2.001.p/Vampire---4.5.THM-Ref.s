%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:10 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 588 expanded)
%              Number of leaves         :   22 ( 188 expanded)
%              Depth                    :   16
%              Number of atoms          :  237 (1191 expanded)
%              Number of equality atoms :  106 ( 768 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f628,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f489,f627])).

fof(f627,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f626])).

fof(f626,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f625,f215])).

fof(f215,plain,(
    r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f107,f206])).

fof(f206,plain,(
    sK0 = sK3(sK1) ),
    inference(unit_resulting_resolution,[],[f175,f104])).

fof(f104,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f70,f88])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).

fof(f44,plain,(
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

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f175,plain,(
    r2_hidden(sK3(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f107,f116,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f116,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f92,f89])).

fof(f89,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f46,f88,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f84])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f46,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f85])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f107,plain,(
    r2_hidden(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f48,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f48,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f625,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f576,f619])).

fof(f619,plain,
    ( sK0 = sK4(sK2,sK1)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f575,f553])).

fof(f553,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK0 = X0 )
    | ~ spl6_2 ),
    inference(superposition,[],[f104,f124])).

fof(f124,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_2
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f575,plain,
    ( r2_hidden(sK4(sK2,sK1),sK2)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f546,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f546,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f47,f119,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f119,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f47,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f576,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f546,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f489,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f477,f355])).

fof(f355,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl6_1 ),
    inference(backward_demodulation,[],[f131,f343])).

fof(f343,plain,
    ( sK0 = sK4(sK1,sK2)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f176,f104])).

fof(f176,plain,
    ( r2_hidden(sK4(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f130,f116,f67])).

fof(f130,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f120,f68])).

fof(f120,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f131,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK2)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f120,f69])).

fof(f477,plain,(
    r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f110,f471])).

fof(f471,plain,(
    sK0 = sK3(sK2) ),
    inference(unit_resulting_resolution,[],[f389,f104])).

fof(f389,plain,(
    r2_hidden(sK3(sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f235,f89])).

fof(f235,plain,(
    ! [X0] : r2_hidden(sK3(sK2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2))) ),
    inference(superposition,[],[f135,f93])).

fof(f93,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f56,f84,f84])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f135,plain,(
    ! [X0] : r2_hidden(sK3(sK2),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0))) ),
    inference(unit_resulting_resolution,[],[f92,f110,f67])).

fof(f110,plain,(
    r2_hidden(sK3(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f49,f52])).

fof(f49,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f126,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f114,f122,f118])).

fof(f114,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f95,f89])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f85])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 12:02:04 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.22/0.50  % (25417)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.50  % (25401)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (25394)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (25399)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (25403)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (25410)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (25404)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (25398)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (25402)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (25415)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (25416)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (25419)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (25405)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (25395)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (25418)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (25396)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (25409)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (25422)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (25400)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (25423)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (25404)Refutation not found, incomplete strategy% (25404)------------------------------
% 0.22/0.54  % (25404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25404)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (25404)Memory used [KB]: 10618
% 0.22/0.54  % (25404)Time elapsed: 0.125 s
% 0.22/0.54  % (25404)------------------------------
% 0.22/0.54  % (25404)------------------------------
% 0.22/0.54  % (25407)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (25413)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (25414)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (25397)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (25421)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (25420)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (25405)Refutation not found, incomplete strategy% (25405)------------------------------
% 0.22/0.55  % (25405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (25405)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (25405)Memory used [KB]: 10874
% 0.22/0.55  % (25405)Time elapsed: 0.121 s
% 0.22/0.55  % (25405)------------------------------
% 0.22/0.55  % (25405)------------------------------
% 0.22/0.55  % (25412)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (25406)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (25411)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.55/0.56  % (25408)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.68/0.63  % (25420)Refutation found. Thanks to Tanya!
% 1.68/0.63  % SZS status Theorem for theBenchmark
% 1.68/0.63  % SZS output start Proof for theBenchmark
% 1.68/0.63  fof(f628,plain,(
% 1.68/0.63    $false),
% 1.68/0.63    inference(avatar_sat_refutation,[],[f126,f489,f627])).
% 1.68/0.63  fof(f627,plain,(
% 1.68/0.63    ~spl6_1 | ~spl6_2),
% 1.68/0.63    inference(avatar_contradiction_clause,[],[f626])).
% 1.68/0.63  fof(f626,plain,(
% 1.68/0.63    $false | (~spl6_1 | ~spl6_2)),
% 1.68/0.63    inference(subsumption_resolution,[],[f625,f215])).
% 1.68/0.63  fof(f215,plain,(
% 1.68/0.63    r2_hidden(sK0,sK1)),
% 1.68/0.63    inference(backward_demodulation,[],[f107,f206])).
% 1.68/0.63  fof(f206,plain,(
% 1.68/0.63    sK0 = sK3(sK1)),
% 1.68/0.63    inference(unit_resulting_resolution,[],[f175,f104])).
% 1.68/0.63  fof(f104,plain,(
% 1.68/0.63    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 1.68/0.63    inference(equality_resolution,[],[f99])).
% 1.68/0.63  fof(f99,plain,(
% 1.68/0.63    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.68/0.63    inference(definition_unfolding,[],[f70,f88])).
% 1.68/0.63  fof(f88,plain,(
% 1.68/0.63    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.68/0.63    inference(definition_unfolding,[],[f51,f84])).
% 1.68/0.63  fof(f84,plain,(
% 1.68/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.68/0.63    inference(definition_unfolding,[],[f58,f83])).
% 1.68/0.63  fof(f83,plain,(
% 1.68/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.68/0.63    inference(definition_unfolding,[],[f74,f82])).
% 1.68/0.63  fof(f82,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.68/0.63    inference(definition_unfolding,[],[f76,f81])).
% 1.68/0.63  fof(f81,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.68/0.63    inference(definition_unfolding,[],[f77,f80])).
% 1.68/0.63  fof(f80,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.68/0.63    inference(definition_unfolding,[],[f78,f79])).
% 1.68/0.63  fof(f79,plain,(
% 1.68/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f22])).
% 1.68/0.63  fof(f22,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.68/0.63  fof(f78,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f21])).
% 1.68/0.63  fof(f21,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.68/0.63  fof(f77,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f20])).
% 1.68/0.63  fof(f20,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.68/0.63  fof(f76,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f19])).
% 1.68/0.63  fof(f19,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.68/0.63  fof(f74,plain,(
% 1.68/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f18])).
% 1.68/0.63  fof(f18,axiom,(
% 1.68/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.68/0.63  fof(f58,plain,(
% 1.68/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f17])).
% 1.68/0.63  fof(f17,axiom,(
% 1.68/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.68/0.63  fof(f51,plain,(
% 1.68/0.63    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f16])).
% 1.68/0.63  fof(f16,axiom,(
% 1.68/0.63    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.68/0.63  fof(f70,plain,(
% 1.68/0.63    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.68/0.63    inference(cnf_transformation,[],[f45])).
% 1.68/0.63  fof(f45,plain,(
% 1.68/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.68/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).
% 2.04/0.63  fof(f44,plain,(
% 2.04/0.63    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 2.04/0.63    introduced(choice_axiom,[])).
% 2.04/0.63  fof(f43,plain,(
% 2.04/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.04/0.63    inference(rectify,[],[f42])).
% 2.04/0.63  fof(f42,plain,(
% 2.04/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.04/0.63    inference(nnf_transformation,[],[f15])).
% 2.04/0.63  fof(f15,axiom,(
% 2.04/0.63    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.04/0.63  fof(f175,plain,(
% 2.04/0.63    r2_hidden(sK3(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f107,f116,f67])).
% 2.04/0.63  fof(f67,plain,(
% 2.04/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f41])).
% 2.04/0.63  fof(f41,plain,(
% 2.04/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 2.04/0.63  fof(f40,plain,(
% 2.04/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.04/0.63    introduced(choice_axiom,[])).
% 2.04/0.63  fof(f39,plain,(
% 2.04/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.63    inference(rectify,[],[f38])).
% 2.04/0.63  fof(f38,plain,(
% 2.04/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.63    inference(nnf_transformation,[],[f31])).
% 2.04/0.63  fof(f31,plain,(
% 2.04/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f2])).
% 2.04/0.63  fof(f2,axiom,(
% 2.04/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.04/0.63  fof(f116,plain,(
% 2.04/0.63    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.04/0.63    inference(superposition,[],[f92,f89])).
% 2.04/0.63  fof(f89,plain,(
% 2.04/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.04/0.63    inference(definition_unfolding,[],[f46,f88,f85])).
% 2.04/0.63  fof(f85,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.04/0.63    inference(definition_unfolding,[],[f59,f84])).
% 2.04/0.63  fof(f59,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f23])).
% 2.04/0.63  fof(f23,axiom,(
% 2.04/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.04/0.63  fof(f46,plain,(
% 2.04/0.63    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.04/0.63    inference(cnf_transformation,[],[f33])).
% 2.04/0.63  fof(f33,plain,(
% 2.04/0.63    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.04/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f32])).
% 2.04/0.63  fof(f32,plain,(
% 2.04/0.63    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.04/0.63    introduced(choice_axiom,[])).
% 2.04/0.63  fof(f28,plain,(
% 2.04/0.63    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.04/0.63    inference(ennf_transformation,[],[f25])).
% 2.04/0.63  fof(f25,negated_conjecture,(
% 2.04/0.63    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.04/0.63    inference(negated_conjecture,[],[f24])).
% 2.04/0.63  fof(f24,conjecture,(
% 2.04/0.63    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 2.04/0.63  fof(f92,plain,(
% 2.04/0.63    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.04/0.63    inference(definition_unfolding,[],[f55,f85])).
% 2.04/0.63  fof(f55,plain,(
% 2.04/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f10])).
% 2.04/0.63  fof(f10,axiom,(
% 2.04/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.04/0.63  fof(f107,plain,(
% 2.04/0.63    r2_hidden(sK3(sK1),sK1)),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f48,f52])).
% 2.04/0.63  fof(f52,plain,(
% 2.04/0.63    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.04/0.63    inference(cnf_transformation,[],[f35])).
% 2.04/0.63  fof(f35,plain,(
% 2.04/0.63    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.04/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f34])).
% 2.04/0.63  fof(f34,plain,(
% 2.04/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.04/0.63    introduced(choice_axiom,[])).
% 2.04/0.63  fof(f29,plain,(
% 2.04/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.04/0.63    inference(ennf_transformation,[],[f5])).
% 2.04/0.63  fof(f5,axiom,(
% 2.04/0.63    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.04/0.63  fof(f48,plain,(
% 2.04/0.63    k1_xboole_0 != sK1),
% 2.04/0.63    inference(cnf_transformation,[],[f33])).
% 2.04/0.63  fof(f625,plain,(
% 2.04/0.63    ~r2_hidden(sK0,sK1) | (~spl6_1 | ~spl6_2)),
% 2.04/0.63    inference(backward_demodulation,[],[f576,f619])).
% 2.04/0.63  fof(f619,plain,(
% 2.04/0.63    sK0 = sK4(sK2,sK1) | (~spl6_1 | ~spl6_2)),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f575,f553])).
% 2.04/0.63  fof(f553,plain,(
% 2.04/0.63    ( ! [X0] : (~r2_hidden(X0,sK2) | sK0 = X0) ) | ~spl6_2),
% 2.04/0.63    inference(superposition,[],[f104,f124])).
% 2.04/0.63  fof(f124,plain,(
% 2.04/0.63    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl6_2),
% 2.04/0.63    inference(avatar_component_clause,[],[f122])).
% 2.04/0.63  fof(f122,plain,(
% 2.04/0.63    spl6_2 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.04/0.63  fof(f575,plain,(
% 2.04/0.63    r2_hidden(sK4(sK2,sK1),sK2) | ~spl6_1),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f546,f68])).
% 2.04/0.63  fof(f68,plain,(
% 2.04/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f41])).
% 2.04/0.63  fof(f546,plain,(
% 2.04/0.63    ~r1_tarski(sK2,sK1) | ~spl6_1),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f47,f119,f66])).
% 2.04/0.63  fof(f66,plain,(
% 2.04/0.63    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f37])).
% 2.04/0.63  fof(f37,plain,(
% 2.04/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.63    inference(flattening,[],[f36])).
% 2.04/0.63  fof(f36,plain,(
% 2.04/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.63    inference(nnf_transformation,[],[f6])).
% 2.04/0.63  fof(f6,axiom,(
% 2.04/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.04/0.63  fof(f119,plain,(
% 2.04/0.63    r1_tarski(sK1,sK2) | ~spl6_1),
% 2.04/0.63    inference(avatar_component_clause,[],[f118])).
% 2.04/0.63  fof(f118,plain,(
% 2.04/0.63    spl6_1 <=> r1_tarski(sK1,sK2)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.04/0.63  fof(f47,plain,(
% 2.04/0.63    sK1 != sK2),
% 2.04/0.63    inference(cnf_transformation,[],[f33])).
% 2.04/0.63  fof(f576,plain,(
% 2.04/0.63    ~r2_hidden(sK4(sK2,sK1),sK1) | ~spl6_1),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f546,f69])).
% 2.04/0.63  fof(f69,plain,(
% 2.04/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f41])).
% 2.04/0.63  fof(f489,plain,(
% 2.04/0.63    spl6_1),
% 2.04/0.63    inference(avatar_contradiction_clause,[],[f488])).
% 2.04/0.63  fof(f488,plain,(
% 2.04/0.63    $false | spl6_1),
% 2.04/0.63    inference(subsumption_resolution,[],[f477,f355])).
% 2.04/0.63  fof(f355,plain,(
% 2.04/0.63    ~r2_hidden(sK0,sK2) | spl6_1),
% 2.04/0.63    inference(backward_demodulation,[],[f131,f343])).
% 2.04/0.63  fof(f343,plain,(
% 2.04/0.63    sK0 = sK4(sK1,sK2) | spl6_1),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f176,f104])).
% 2.04/0.63  fof(f176,plain,(
% 2.04/0.63    r2_hidden(sK4(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl6_1),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f130,f116,f67])).
% 2.04/0.63  fof(f130,plain,(
% 2.04/0.63    r2_hidden(sK4(sK1,sK2),sK1) | spl6_1),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f120,f68])).
% 2.04/0.63  fof(f120,plain,(
% 2.04/0.63    ~r1_tarski(sK1,sK2) | spl6_1),
% 2.04/0.63    inference(avatar_component_clause,[],[f118])).
% 2.04/0.63  fof(f131,plain,(
% 2.04/0.63    ~r2_hidden(sK4(sK1,sK2),sK2) | spl6_1),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f120,f69])).
% 2.04/0.63  fof(f477,plain,(
% 2.04/0.63    r2_hidden(sK0,sK2)),
% 2.04/0.63    inference(backward_demodulation,[],[f110,f471])).
% 2.04/0.63  fof(f471,plain,(
% 2.04/0.63    sK0 = sK3(sK2)),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f389,f104])).
% 2.04/0.63  fof(f389,plain,(
% 2.04/0.63    r2_hidden(sK3(sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.04/0.63    inference(superposition,[],[f235,f89])).
% 2.04/0.63  fof(f235,plain,(
% 2.04/0.63    ( ! [X0] : (r2_hidden(sK3(sK2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)))) )),
% 2.04/0.63    inference(superposition,[],[f135,f93])).
% 2.04/0.63  fof(f93,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 2.04/0.63    inference(definition_unfolding,[],[f56,f84,f84])).
% 2.04/0.63  fof(f56,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f14])).
% 2.04/0.63  fof(f14,axiom,(
% 2.04/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.04/0.63  fof(f135,plain,(
% 2.04/0.63    ( ! [X0] : (r2_hidden(sK3(sK2),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))) )),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f92,f110,f67])).
% 2.04/0.63  fof(f110,plain,(
% 2.04/0.63    r2_hidden(sK3(sK2),sK2)),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f49,f52])).
% 2.04/0.63  fof(f49,plain,(
% 2.04/0.63    k1_xboole_0 != sK2),
% 2.04/0.63    inference(cnf_transformation,[],[f33])).
% 2.04/0.63  fof(f126,plain,(
% 2.04/0.63    ~spl6_1 | spl6_2),
% 2.04/0.63    inference(avatar_split_clause,[],[f114,f122,f118])).
% 2.04/0.63  fof(f114,plain,(
% 2.04/0.63    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2)),
% 2.04/0.63    inference(superposition,[],[f95,f89])).
% 2.04/0.63  fof(f95,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.04/0.63    inference(definition_unfolding,[],[f63,f85])).
% 2.04/0.63  fof(f63,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f30])).
% 2.04/0.63  fof(f30,plain,(
% 2.04/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.04/0.63    inference(ennf_transformation,[],[f8])).
% 2.04/0.63  fof(f8,axiom,(
% 2.04/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.04/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.04/0.63  % SZS output end Proof for theBenchmark
% 2.04/0.63  % (25420)------------------------------
% 2.04/0.63  % (25420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.63  % (25420)Termination reason: Refutation
% 2.04/0.63  
% 2.04/0.63  % (25420)Memory used [KB]: 11385
% 2.04/0.63  % (25420)Time elapsed: 0.185 s
% 2.04/0.63  % (25420)------------------------------
% 2.04/0.63  % (25420)------------------------------
% 2.04/0.63  % (25390)Success in time 0.269 s
%------------------------------------------------------------------------------
