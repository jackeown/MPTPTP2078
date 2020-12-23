%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:26 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 240 expanded)
%              Number of leaves         :   22 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  311 ( 787 expanded)
%              Number of equality atoms :   26 (  73 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1209,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f643,f911,f944,f1208])).

fof(f1208,plain,(
    spl9_20 ),
    inference(avatar_contradiction_clause,[],[f1207])).

fof(f1207,plain,
    ( $false
    | spl9_20 ),
    inference(subsumption_resolution,[],[f1206,f1198])).

fof(f1198,plain,
    ( r2_hidden(sK5,sK2)
    | spl9_20 ),
    inference(resolution,[],[f1185,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1185,plain,
    ( sP0(k4_xboole_0(sK2,sK3),sK5,sK2)
    | spl9_20 ),
    inference(resolution,[],[f1171,f356])).

fof(f356,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(resolution,[],[f71,f88])).

fof(f88,plain,(
    ! [X0,X1] : sP1(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f27,f26])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sP0(X1,sK8(X0,X1,X2),X0)
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sP0(X1,sK8(X0,X1,X2),X0)
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f1171,plain,
    ( r2_hidden(sK5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | spl9_20 ),
    inference(resolution,[],[f638,f485])).

fof(f485,plain,(
    ! [X6,X5] :
      ( r1_xboole_0(X5,k2_enumset1(X6,X6,X6,X6))
      | r2_hidden(X6,X5) ) ),
    inference(trivial_inequality_removal,[],[f477])).

fof(f477,plain,(
    ! [X6,X5] :
      ( X5 != X5
      | r1_xboole_0(X5,k2_enumset1(X6,X6,X6,X6))
      | r2_hidden(X6,X5) ) ),
    inference(superposition,[],[f64,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f66,f80])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f638,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5))
    | spl9_20 ),
    inference(avatar_component_clause,[],[f636])).

fof(f636,plain,
    ( spl9_20
  <=> r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f1206,plain,
    ( ~ r2_hidden(sK5,sK2)
    | spl9_20 ),
    inference(subsumption_resolution,[],[f1205,f145])).

fof(f145,plain,(
    ~ r2_hidden(sK5,sK3) ),
    inference(resolution,[],[f138,f47])).

fof(f47,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f138,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f59,f48])).

fof(f48,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1205,plain,
    ( r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK5,sK2)
    | spl9_20 ),
    inference(resolution,[],[f1202,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1202,plain,
    ( ~ sP0(sK3,sK5,sK2)
    | spl9_20 ),
    inference(resolution,[],[f1197,f384])).

fof(f384,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k4_xboole_0(X2,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f72,f88])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1197,plain,
    ( ~ r2_hidden(sK5,k4_xboole_0(sK2,sK3))
    | spl9_20 ),
    inference(resolution,[],[f1185,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f944,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f943,f96])).

fof(f96,plain,
    ( spl9_1
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f943,plain,(
    ~ r1_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f922,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f922,plain,(
    ~ r1_xboole_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f315,f153])).

fof(f153,plain,(
    r1_xboole_0(sK3,sK4) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,
    ( r1_xboole_0(sK3,sK4)
    | r1_xboole_0(sK3,sK4) ),
    inference(resolution,[],[f147,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f147,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK7(X1,sK4),sK3)
      | r1_xboole_0(X1,sK4) ) ),
    inference(resolution,[],[f138,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f315,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK3,sK4) ),
    inference(resolution,[],[f67,f89])).

fof(f89,plain,(
    ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(resolution,[],[f60,f49])).

fof(f49,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f911,plain,
    ( spl9_1
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f897,f641,f96])).

fof(f641,plain,
    ( spl9_21
  <=> ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f897,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl9_21 ),
    inference(resolution,[],[f642,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f642,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f641])).

fof(f643,plain,
    ( spl9_21
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f622,f636,f641])).

fof(f622,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5))
      | ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ) ),
    inference(resolution,[],[f539,f202])).

fof(f202,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X4)
      | ~ r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f197,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f197,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k4_xboole_0(X0,X0)) ),
    inference(subsumption_resolution,[],[f191,f115])).

fof(f115,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,(
    ! [X0] :
      ( X0 != X0
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f64,f50])).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(X0,X0))
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f82,f50])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f53])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f539,plain,(
    ! [X0] :
      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0)
      | ~ r1_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5)) ) ),
    inference(resolution,[],[f130,f81])).

fof(f81,plain,(
    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f46,f53,f80])).

fof(f46,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f30])).

fof(f130,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X3)
      | r1_xboole_0(X4,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f70,f63])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.52  % (28808)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (28817)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (28825)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (28807)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (28810)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (28816)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (28809)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (28813)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (28802)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (28824)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (28830)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (28806)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (28828)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (28805)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (28804)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (28822)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.55  % (28831)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.55  % (28820)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.56  % (28829)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.56  % (28823)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.56  % (28814)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.56  % (28812)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.56  % (28826)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.57  % (28815)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.57  % (28821)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.57  % (28827)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.57  % (28811)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.57  % (28818)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.59  % (28819)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.59/0.59  % (28803)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.03/0.64  % (28829)Refutation found. Thanks to Tanya!
% 2.03/0.64  % SZS status Theorem for theBenchmark
% 2.03/0.64  % SZS output start Proof for theBenchmark
% 2.03/0.64  fof(f1209,plain,(
% 2.03/0.64    $false),
% 2.03/0.64    inference(avatar_sat_refutation,[],[f643,f911,f944,f1208])).
% 2.03/0.64  fof(f1208,plain,(
% 2.03/0.64    spl9_20),
% 2.03/0.64    inference(avatar_contradiction_clause,[],[f1207])).
% 2.03/0.64  fof(f1207,plain,(
% 2.03/0.64    $false | spl9_20),
% 2.03/0.64    inference(subsumption_resolution,[],[f1206,f1198])).
% 2.03/0.64  fof(f1198,plain,(
% 2.03/0.64    r2_hidden(sK5,sK2) | spl9_20),
% 2.03/0.64    inference(resolution,[],[f1185,f75])).
% 2.03/0.64  fof(f75,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f44])).
% 2.03/0.64  fof(f44,plain,(
% 2.03/0.64    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 2.03/0.64    inference(rectify,[],[f43])).
% 2.03/0.64  fof(f43,plain,(
% 2.03/0.64    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 2.03/0.64    inference(flattening,[],[f42])).
% 2.03/0.64  fof(f42,plain,(
% 2.03/0.64    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 2.03/0.64    inference(nnf_transformation,[],[f26])).
% 2.03/0.64  fof(f26,plain,(
% 2.03/0.64    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 2.03/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.03/0.64  fof(f1185,plain,(
% 2.03/0.64    sP0(k4_xboole_0(sK2,sK3),sK5,sK2) | spl9_20),
% 2.03/0.64    inference(resolution,[],[f1171,f356])).
% 2.03/0.64  fof(f356,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 2.03/0.64    inference(resolution,[],[f71,f88])).
% 2.03/0.64  fof(f88,plain,(
% 2.03/0.64    ( ! [X0,X1] : (sP1(X0,X1,k4_xboole_0(X0,X1))) )),
% 2.03/0.64    inference(equality_resolution,[],[f78])).
% 2.03/0.64  fof(f78,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.03/0.64    inference(cnf_transformation,[],[f45])).
% 2.03/0.64  fof(f45,plain,(
% 2.03/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 2.03/0.64    inference(nnf_transformation,[],[f28])).
% 2.03/0.64  fof(f28,plain,(
% 2.03/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 2.03/0.64    inference(definition_folding,[],[f2,f27,f26])).
% 2.03/0.64  fof(f27,plain,(
% 2.03/0.64    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 2.03/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.03/0.64  fof(f2,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.03/0.64  fof(f71,plain,(
% 2.03/0.64    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f41])).
% 2.03/0.64  fof(f41,plain,(
% 2.03/0.64    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP0(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).
% 2.03/0.64  fof(f40,plain,(
% 2.03/0.64    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP0(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f39,plain,(
% 2.03/0.64    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.03/0.64    inference(rectify,[],[f38])).
% 2.03/0.64  fof(f38,plain,(
% 2.03/0.64    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 2.03/0.64    inference(nnf_transformation,[],[f27])).
% 2.03/0.64  fof(f1171,plain,(
% 2.03/0.64    r2_hidden(sK5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) | spl9_20),
% 2.03/0.64    inference(resolution,[],[f638,f485])).
% 2.03/0.64  fof(f485,plain,(
% 2.03/0.64    ( ! [X6,X5] : (r1_xboole_0(X5,k2_enumset1(X6,X6,X6,X6)) | r2_hidden(X6,X5)) )),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f477])).
% 2.03/0.64  fof(f477,plain,(
% 2.03/0.64    ( ! [X6,X5] : (X5 != X5 | r1_xboole_0(X5,k2_enumset1(X6,X6,X6,X6)) | r2_hidden(X6,X5)) )),
% 2.03/0.64    inference(superposition,[],[f64,f86])).
% 2.03/0.64  fof(f86,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f66,f80])).
% 2.03/0.64  fof(f80,plain,(
% 2.03/0.64    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f51,f54])).
% 2.03/0.64  fof(f54,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f13])).
% 2.03/0.64  fof(f13,axiom,(
% 2.03/0.64    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 2.03/0.64  fof(f51,plain,(
% 2.03/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f12])).
% 2.03/0.64  fof(f12,axiom,(
% 2.03/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.03/0.64  fof(f66,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f37])).
% 2.03/0.64  fof(f37,plain,(
% 2.03/0.64    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.03/0.64    inference(nnf_transformation,[],[f14])).
% 2.03/0.64  fof(f14,axiom,(
% 2.03/0.64    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 2.03/0.64  fof(f64,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f36])).
% 2.03/0.64  fof(f36,plain,(
% 2.03/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.03/0.64    inference(nnf_transformation,[],[f10])).
% 2.03/0.64  fof(f10,axiom,(
% 2.03/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.03/0.64  fof(f638,plain,(
% 2.03/0.64    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) | spl9_20),
% 2.03/0.64    inference(avatar_component_clause,[],[f636])).
% 2.03/0.64  fof(f636,plain,(
% 2.03/0.64    spl9_20 <=> r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 2.03/0.64  fof(f1206,plain,(
% 2.03/0.64    ~r2_hidden(sK5,sK2) | spl9_20),
% 2.03/0.64    inference(subsumption_resolution,[],[f1205,f145])).
% 2.03/0.64  fof(f145,plain,(
% 2.03/0.64    ~r2_hidden(sK5,sK3)),
% 2.03/0.64    inference(resolution,[],[f138,f47])).
% 2.03/0.64  fof(f47,plain,(
% 2.03/0.64    r2_hidden(sK5,sK4)),
% 2.03/0.64    inference(cnf_transformation,[],[f30])).
% 2.03/0.64  fof(f30,plain,(
% 2.03/0.64    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f29])).
% 2.03/0.64  fof(f29,plain,(
% 2.03/0.64    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f20,plain,(
% 2.03/0.64    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 2.03/0.64    inference(flattening,[],[f19])).
% 2.03/0.64  fof(f19,plain,(
% 2.03/0.64    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 2.03/0.64    inference(ennf_transformation,[],[f16])).
% 2.03/0.64  fof(f16,negated_conjecture,(
% 2.03/0.64    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.03/0.64    inference(negated_conjecture,[],[f15])).
% 2.03/0.64  fof(f15,conjecture,(
% 2.03/0.64    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 2.03/0.64  fof(f138,plain,(
% 2.03/0.64    ( ! [X0] : (~r2_hidden(X0,sK4) | ~r2_hidden(X0,sK3)) )),
% 2.03/0.64    inference(resolution,[],[f59,f48])).
% 2.03/0.64  fof(f48,plain,(
% 2.03/0.64    r1_xboole_0(sK4,sK3)),
% 2.03/0.64    inference(cnf_transformation,[],[f30])).
% 2.03/0.64  fof(f59,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f34])).
% 2.03/0.64  fof(f34,plain,(
% 2.03/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f33])).
% 2.03/0.64  fof(f33,plain,(
% 2.03/0.64    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f22,plain,(
% 2.03/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.03/0.64    inference(ennf_transformation,[],[f18])).
% 2.03/0.64  fof(f18,plain,(
% 2.03/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.64    inference(rectify,[],[f5])).
% 2.03/0.64  fof(f5,axiom,(
% 2.03/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.03/0.64  fof(f1205,plain,(
% 2.03/0.64    r2_hidden(sK5,sK3) | ~r2_hidden(sK5,sK2) | spl9_20),
% 2.03/0.64    inference(resolution,[],[f1202,f77])).
% 2.03/0.64  fof(f77,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f44])).
% 2.03/0.64  fof(f1202,plain,(
% 2.03/0.64    ~sP0(sK3,sK5,sK2) | spl9_20),
% 2.03/0.64    inference(resolution,[],[f1197,f384])).
% 2.03/0.64  fof(f384,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (r2_hidden(X1,k4_xboole_0(X2,X0)) | ~sP0(X0,X1,X2)) )),
% 2.03/0.64    inference(resolution,[],[f72,f88])).
% 2.03/0.64  fof(f72,plain,(
% 2.03/0.64    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f41])).
% 2.03/0.64  fof(f1197,plain,(
% 2.03/0.64    ~r2_hidden(sK5,k4_xboole_0(sK2,sK3)) | spl9_20),
% 2.03/0.64    inference(resolution,[],[f1185,f76])).
% 2.03/0.64  fof(f76,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f44])).
% 2.03/0.64  fof(f944,plain,(
% 2.03/0.64    ~spl9_1),
% 2.03/0.64    inference(avatar_split_clause,[],[f943,f96])).
% 2.03/0.64  fof(f96,plain,(
% 2.03/0.64    spl9_1 <=> r1_xboole_0(sK2,sK3)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 2.03/0.64  fof(f943,plain,(
% 2.03/0.64    ~r1_xboole_0(sK2,sK3)),
% 2.03/0.64    inference(resolution,[],[f922,f60])).
% 2.03/0.64  fof(f60,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f23])).
% 2.03/0.64  fof(f23,plain,(
% 2.03/0.64    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.03/0.64    inference(ennf_transformation,[],[f4])).
% 2.03/0.64  fof(f4,axiom,(
% 2.03/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.03/0.64  fof(f922,plain,(
% 2.03/0.64    ~r1_xboole_0(sK3,sK2)),
% 2.03/0.64    inference(subsumption_resolution,[],[f315,f153])).
% 2.03/0.64  fof(f153,plain,(
% 2.03/0.64    r1_xboole_0(sK3,sK4)),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f152])).
% 2.03/0.64  fof(f152,plain,(
% 2.03/0.64    r1_xboole_0(sK3,sK4) | r1_xboole_0(sK3,sK4)),
% 2.03/0.64    inference(resolution,[],[f147,f57])).
% 2.03/0.64  fof(f57,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f34])).
% 2.03/0.64  fof(f147,plain,(
% 2.03/0.64    ( ! [X1] : (~r2_hidden(sK7(X1,sK4),sK3) | r1_xboole_0(X1,sK4)) )),
% 2.03/0.64    inference(resolution,[],[f138,f58])).
% 2.03/0.64  fof(f58,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f34])).
% 2.03/0.64  fof(f315,plain,(
% 2.03/0.64    ~r1_xboole_0(sK3,sK2) | ~r1_xboole_0(sK3,sK4)),
% 2.03/0.64    inference(resolution,[],[f67,f89])).
% 2.03/0.64  fof(f89,plain,(
% 2.03/0.64    ~r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))),
% 2.03/0.64    inference(resolution,[],[f60,f49])).
% 2.03/0.64  fof(f49,plain,(
% 2.03/0.64    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 2.03/0.64    inference(cnf_transformation,[],[f30])).
% 2.03/0.64  fof(f67,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f24])).
% 2.03/0.64  fof(f24,plain,(
% 2.03/0.64    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.03/0.64    inference(ennf_transformation,[],[f9])).
% 2.03/0.64  fof(f9,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.03/0.64  fof(f911,plain,(
% 2.03/0.64    spl9_1 | ~spl9_21),
% 2.03/0.64    inference(avatar_split_clause,[],[f897,f641,f96])).
% 2.03/0.64  fof(f641,plain,(
% 2.03/0.64    spl9_21 <=> ! [X0] : ~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 2.03/0.64  fof(f897,plain,(
% 2.03/0.64    r1_xboole_0(sK2,sK3) | ~spl9_21),
% 2.03/0.64    inference(resolution,[],[f642,f83])).
% 2.03/0.64  fof(f83,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f55,f53])).
% 2.03/0.64  fof(f53,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f8])).
% 2.03/0.64  fof(f8,axiom,(
% 2.03/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.03/0.64  fof(f55,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f32])).
% 2.03/0.64  fof(f32,plain,(
% 2.03/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f31])).
% 2.03/0.64  fof(f31,plain,(
% 2.03/0.64    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f21,plain,(
% 2.03/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.03/0.64    inference(ennf_transformation,[],[f17])).
% 2.03/0.64  fof(f17,plain,(
% 2.03/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.64    inference(rectify,[],[f6])).
% 2.03/0.64  fof(f6,axiom,(
% 2.03/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.03/0.64  fof(f642,plain,(
% 2.03/0.64    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) ) | ~spl9_21),
% 2.03/0.64    inference(avatar_component_clause,[],[f641])).
% 2.03/0.64  fof(f643,plain,(
% 2.03/0.64    spl9_21 | ~spl9_20),
% 2.03/0.64    inference(avatar_split_clause,[],[f622,f636,f641])).
% 2.03/0.64  fof(f622,plain,(
% 2.03/0.64    ( ! [X0] : (~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) | ~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) )),
% 2.03/0.64    inference(resolution,[],[f539,f202])).
% 2.03/0.64  fof(f202,plain,(
% 2.03/0.64    ( ! [X4,X5] : (~r1_xboole_0(X4,X4) | ~r2_hidden(X5,X4)) )),
% 2.03/0.64    inference(superposition,[],[f197,f63])).
% 2.03/0.64  fof(f63,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f36])).
% 2.03/0.64  fof(f197,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0))) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f191,f115])).
% 2.03/0.64  fof(f115,plain,(
% 2.03/0.64    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.03/0.64    inference(trivial_inequality_removal,[],[f113])).
% 2.03/0.64  fof(f113,plain,(
% 2.03/0.64    ( ! [X0] : (X0 != X0 | r1_xboole_0(X0,k1_xboole_0)) )),
% 2.03/0.64    inference(superposition,[],[f64,f50])).
% 2.03/0.64  fof(f50,plain,(
% 2.03/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f7])).
% 2.03/0.64  fof(f7,axiom,(
% 2.03/0.64    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.03/0.64  fof(f191,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0)) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 2.03/0.64    inference(superposition,[],[f82,f50])).
% 2.03/0.64  fof(f82,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f56,f53])).
% 2.03/0.64  fof(f56,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f32])).
% 2.03/0.64  fof(f539,plain,(
% 2.03/0.64    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0) | ~r1_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) )),
% 2.03/0.64    inference(resolution,[],[f130,f81])).
% 2.03/0.64  fof(f81,plain,(
% 2.03/0.64    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5))),
% 2.03/0.64    inference(definition_unfolding,[],[f46,f53,f80])).
% 2.03/0.64  fof(f46,plain,(
% 2.03/0.64    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 2.03/0.64    inference(cnf_transformation,[],[f30])).
% 2.03/0.64  fof(f130,plain,(
% 2.03/0.64    ( ! [X4,X2,X3] : (~r1_tarski(X4,X3) | r1_xboole_0(X4,X2) | ~r1_xboole_0(X2,X3)) )),
% 2.03/0.64    inference(superposition,[],[f70,f63])).
% 2.03/0.64  fof(f70,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f25])).
% 2.03/0.64  fof(f25,plain,(
% 2.03/0.64    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.03/0.64    inference(ennf_transformation,[],[f11])).
% 2.03/0.64  fof(f11,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.03/0.64  % SZS output end Proof for theBenchmark
% 2.03/0.64  % (28829)------------------------------
% 2.03/0.64  % (28829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.64  % (28829)Termination reason: Refutation
% 2.03/0.64  
% 2.03/0.64  % (28829)Memory used [KB]: 6652
% 2.03/0.64  % (28829)Time elapsed: 0.190 s
% 2.03/0.64  % (28829)------------------------------
% 2.03/0.64  % (28829)------------------------------
% 2.03/0.64  % (28801)Success in time 0.27 s
%------------------------------------------------------------------------------
