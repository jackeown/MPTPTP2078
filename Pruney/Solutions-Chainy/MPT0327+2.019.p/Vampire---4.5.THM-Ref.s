%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:50 EST 2020

% Result     : Theorem 6.84s
% Output     : Refutation 6.84s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 408 expanded)
%              Number of leaves         :   20 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :  306 ( 942 expanded)
%              Number of equality atoms :   70 ( 369 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f208,f229,f230,f876,f952,f2096,f2098,f2188])).

fof(f2188,plain,
    ( spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f2179,f226,f201])).

fof(f201,plain,
    ( spl3_5
  <=> r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f226,plain,
    ( spl3_7
  <=> r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f2179,plain,
    ( r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1)
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f228,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) ) ),
    inference(definition_unfolding,[],[f58,f40,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f228,plain,
    ( r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f226])).

fof(f2098,plain,
    ( ~ spl3_6
    | spl3_25 ),
    inference(avatar_contradiction_clause,[],[f2097])).

fof(f2097,plain,
    ( $false
    | ~ spl3_6
    | spl3_25 ),
    inference(subsumption_resolution,[],[f1003,f2095])).

fof(f2095,plain,
    ( ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k1_xboole_0))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f2093])).

fof(f2093,plain,
    ( spl3_25
  <=> r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f1003,plain,
    ( r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f206,f383])).

fof(f383,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | r2_hidden(X4,k5_xboole_0(sK1,k1_xboole_0)) ) ),
    inference(superposition,[],[f87,f327])).

fof(f327,plain,(
    k5_xboole_0(sK1,k1_xboole_0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f69,f114])).

fof(f114,plain,(
    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f94,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f94,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f33,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f33,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f69,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f41,f64,f40])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f63])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f206,plain,
    ( r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl3_6
  <=> r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f2096,plain,
    ( ~ spl3_19
    | ~ spl3_25
    | spl3_5 ),
    inference(avatar_split_clause,[],[f2087,f201,f2093,f849])).

fof(f849,plain,
    ( spl3_19
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f2087,plain,
    ( ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k1_xboole_0))
    | ~ r1_tarski(sK1,sK1)
    | spl3_5 ),
    inference(superposition,[],[f979,f74])).

fof(f979,plain,
    ( ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))))
    | spl3_5 ),
    inference(forward_demodulation,[],[f973,f69])).

fof(f973,plain,
    ( ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f203,f203,f89])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f52,f64])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f203,plain,
    ( ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f201])).

fof(f952,plain,
    ( ~ spl3_5
    | spl3_6
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f951])).

fof(f951,plain,
    ( $false
    | ~ spl3_5
    | spl3_6
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f86,f916,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f916,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_5
    | spl3_6
    | spl3_7 ),
    inference(superposition,[],[f207,f453])).

fof(f453,plain,
    ( sK0 = sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl3_5
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f202,f227,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f40,f65])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f227,plain,
    ( ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f226])).

fof(f202,plain,
    ( r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f201])).

fof(f207,plain,
    ( ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f205])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f876,plain,(
    spl3_19 ),
    inference(avatar_contradiction_clause,[],[f874])).

fof(f874,plain,
    ( $false
    | spl3_19 ),
    inference(unit_resulting_resolution,[],[f86,f851])).

fof(f851,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f849])).

fof(f230,plain,
    ( ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f217,f226,f201])).

fof(f217,plain,
    ( ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
    | ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X1] :
      ( sK1 != X1
      | ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X1),X1) ) ),
    inference(superposition,[],[f66,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f34,f64,f40,f65,f65])).

fof(f34,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f229,plain,
    ( spl3_5
    | spl3_7
    | spl3_6 ),
    inference(avatar_split_clause,[],[f224,f205,f226,f201])).

fof(f224,plain,
    ( r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
    | r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2] :
      ( sK1 != X2
      | r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X2),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X2),X2) ) ),
    inference(superposition,[],[f66,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f208,plain,
    ( ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f199,f205,f201])).

fof(f199,plain,
    ( ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0),X0) ) ),
    inference(superposition,[],[f66,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f57,f64])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:59:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (27076)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.50  % (27106)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.50  % (27075)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.50  % (27077)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (27078)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (27095)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (27073)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (27074)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (27086)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (27087)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (27072)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (27107)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (27099)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (27100)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (27092)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (27103)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (27106)Refutation not found, incomplete strategy% (27106)------------------------------
% 0.21/0.53  % (27106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27106)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27106)Memory used [KB]: 10874
% 0.21/0.53  % (27106)Time elapsed: 0.116 s
% 0.21/0.53  % (27106)------------------------------
% 0.21/0.53  % (27106)------------------------------
% 0.21/0.53  % (27090)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (27107)Refutation not found, incomplete strategy% (27107)------------------------------
% 0.21/0.53  % (27107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27107)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27107)Memory used [KB]: 1663
% 0.21/0.53  % (27107)Time elapsed: 0.101 s
% 0.21/0.53  % (27107)------------------------------
% 0.21/0.53  % (27107)------------------------------
% 0.21/0.53  % (27091)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (27084)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (27091)Refutation not found, incomplete strategy% (27091)------------------------------
% 0.21/0.53  % (27091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27091)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27091)Memory used [KB]: 10618
% 0.21/0.53  % (27091)Time elapsed: 0.139 s
% 0.21/0.53  % (27091)------------------------------
% 0.21/0.53  % (27091)------------------------------
% 0.21/0.54  % (27084)Refutation not found, incomplete strategy% (27084)------------------------------
% 0.21/0.54  % (27084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27084)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27084)Memory used [KB]: 10874
% 0.21/0.54  % (27084)Time elapsed: 0.140 s
% 0.21/0.54  % (27084)------------------------------
% 0.21/0.54  % (27084)------------------------------
% 0.21/0.54  % (27083)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (27102)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (27105)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (27093)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (27094)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (27097)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (27088)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (27089)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (27089)Refutation not found, incomplete strategy% (27089)------------------------------
% 0.21/0.54  % (27089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27080)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (27089)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27089)Memory used [KB]: 1663
% 0.21/0.54  % (27089)Time elapsed: 0.102 s
% 0.21/0.54  % (27089)------------------------------
% 0.21/0.54  % (27089)------------------------------
% 0.21/0.54  % (27101)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (27082)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (27093)Refutation not found, incomplete strategy% (27093)------------------------------
% 0.21/0.54  % (27093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27101)Refutation not found, incomplete strategy% (27101)------------------------------
% 0.21/0.55  % (27101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27093)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27093)Memory used [KB]: 1663
% 0.21/0.55  % (27093)Time elapsed: 0.151 s
% 0.21/0.55  % (27093)------------------------------
% 0.21/0.55  % (27093)------------------------------
% 0.21/0.55  % (27092)Refutation not found, incomplete strategy% (27092)------------------------------
% 0.21/0.55  % (27092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27092)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27092)Memory used [KB]: 1791
% 0.21/0.55  % (27092)Time elapsed: 0.162 s
% 0.21/0.55  % (27092)------------------------------
% 0.21/0.55  % (27092)------------------------------
% 0.21/0.55  % (27105)Refutation not found, incomplete strategy% (27105)------------------------------
% 0.21/0.55  % (27105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27105)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27105)Memory used [KB]: 6140
% 0.21/0.55  % (27105)Time elapsed: 0.160 s
% 0.21/0.55  % (27105)------------------------------
% 0.21/0.55  % (27105)------------------------------
% 0.21/0.56  % (27101)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (27101)Memory used [KB]: 10746
% 0.21/0.56  % (27101)Time elapsed: 0.153 s
% 0.21/0.56  % (27101)------------------------------
% 0.21/0.56  % (27101)------------------------------
% 2.12/0.65  % (27148)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.12/0.65  % (27150)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.12/0.66  % (27151)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.12/0.67  % (27152)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.12/0.67  % (27154)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.12/0.69  % (27153)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.12/0.69  % (27155)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.12/0.69  % (27149)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.12/0.69  % (27152)Refutation not found, incomplete strategy% (27152)------------------------------
% 2.12/0.69  % (27152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.69  % (27152)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.69  
% 2.12/0.69  % (27152)Memory used [KB]: 10746
% 2.12/0.69  % (27152)Time elapsed: 0.110 s
% 2.12/0.69  % (27152)------------------------------
% 2.12/0.69  % (27152)------------------------------
% 2.12/0.69  % (27156)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.33/0.80  % (27074)Time limit reached!
% 3.33/0.80  % (27074)------------------------------
% 3.33/0.80  % (27074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.80  % (27074)Termination reason: Time limit
% 3.33/0.80  % (27074)Termination phase: Saturation
% 3.33/0.80  
% 3.33/0.80  % (27074)Memory used [KB]: 7547
% 3.33/0.80  % (27074)Time elapsed: 0.400 s
% 3.33/0.80  % (27074)------------------------------
% 3.33/0.80  % (27074)------------------------------
% 3.33/0.83  % (27162)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.33/0.85  % (27162)Refutation not found, incomplete strategy% (27162)------------------------------
% 3.33/0.85  % (27162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.85  % (27162)Termination reason: Refutation not found, incomplete strategy
% 3.33/0.85  
% 3.33/0.85  % (27162)Memory used [KB]: 10746
% 3.33/0.85  % (27162)Time elapsed: 0.136 s
% 3.33/0.85  % (27162)------------------------------
% 3.33/0.85  % (27162)------------------------------
% 4.37/0.92  % (27078)Time limit reached!
% 4.37/0.92  % (27078)------------------------------
% 4.37/0.92  % (27078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.92  % (27078)Termination reason: Time limit
% 4.37/0.92  
% 4.37/0.92  % (27078)Memory used [KB]: 14967
% 4.37/0.92  % (27078)Time elapsed: 0.518 s
% 4.37/0.92  % (27078)------------------------------
% 4.37/0.92  % (27078)------------------------------
% 4.46/0.94  % (27169)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 4.46/0.99  % (27170)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 5.04/1.03  % (27080)Time limit reached!
% 5.04/1.03  % (27080)------------------------------
% 5.04/1.03  % (27080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.04/1.03  % (27080)Termination reason: Time limit
% 5.04/1.03  
% 5.04/1.03  % (27080)Memory used [KB]: 4733
% 5.04/1.03  % (27080)Time elapsed: 0.607 s
% 5.04/1.03  % (27080)------------------------------
% 5.04/1.03  % (27080)------------------------------
% 5.04/1.06  % (27171)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 5.57/1.17  % (27172)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 5.57/1.17  % (27154)Time limit reached!
% 5.57/1.17  % (27154)------------------------------
% 5.57/1.17  % (27154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.57/1.17  % (27154)Termination reason: Time limit
% 5.57/1.17  % (27154)Termination phase: Saturation
% 5.57/1.17  
% 5.57/1.17  % (27154)Memory used [KB]: 18421
% 5.57/1.17  % (27154)Time elapsed: 0.600 s
% 5.57/1.17  % (27154)------------------------------
% 5.57/1.17  % (27154)------------------------------
% 6.66/1.21  % (27073)Time limit reached!
% 6.66/1.21  % (27073)------------------------------
% 6.66/1.21  % (27073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.66/1.21  % (27073)Termination reason: Time limit
% 6.66/1.21  
% 6.66/1.21  % (27073)Memory used [KB]: 5500
% 6.66/1.21  % (27073)Time elapsed: 0.816 s
% 6.66/1.21  % (27073)------------------------------
% 6.66/1.21  % (27073)------------------------------
% 6.84/1.26  % (27170)Refutation found. Thanks to Tanya!
% 6.84/1.26  % SZS status Theorem for theBenchmark
% 6.84/1.26  % SZS output start Proof for theBenchmark
% 6.84/1.26  fof(f2189,plain,(
% 6.84/1.26    $false),
% 6.84/1.26    inference(avatar_sat_refutation,[],[f208,f229,f230,f876,f952,f2096,f2098,f2188])).
% 6.84/1.26  fof(f2188,plain,(
% 6.84/1.26    spl3_5 | ~spl3_7),
% 6.84/1.26    inference(avatar_split_clause,[],[f2179,f226,f201])).
% 6.84/1.26  fof(f201,plain,(
% 6.84/1.26    spl3_5 <=> r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1)),
% 6.84/1.26    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 6.84/1.26  fof(f226,plain,(
% 6.84/1.26    spl3_7 <=> r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 6.84/1.26    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 6.84/1.26  fof(f2179,plain,(
% 6.84/1.26    r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1) | ~spl3_7),
% 6.84/1.26    inference(unit_resulting_resolution,[],[f228,f84])).
% 6.84/1.26  fof(f84,plain,(
% 6.84/1.26    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))))) )),
% 6.84/1.26    inference(definition_unfolding,[],[f58,f40,f65])).
% 6.84/1.26  fof(f65,plain,(
% 6.84/1.26    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 6.84/1.26    inference(definition_unfolding,[],[f36,f63])).
% 6.84/1.26  fof(f63,plain,(
% 6.84/1.26    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 6.84/1.26    inference(definition_unfolding,[],[f39,f62])).
% 6.84/1.26  fof(f62,plain,(
% 6.84/1.26    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 6.84/1.26    inference(definition_unfolding,[],[f51,f61])).
% 6.84/1.26  fof(f61,plain,(
% 6.84/1.26    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 6.84/1.26    inference(cnf_transformation,[],[f13])).
% 6.84/1.26  fof(f13,axiom,(
% 6.84/1.26    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 6.84/1.26  fof(f51,plain,(
% 6.84/1.26    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 6.84/1.26    inference(cnf_transformation,[],[f12])).
% 6.84/1.26  fof(f12,axiom,(
% 6.84/1.26    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 6.84/1.26  fof(f39,plain,(
% 6.84/1.26    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.84/1.26    inference(cnf_transformation,[],[f11])).
% 6.84/1.26  fof(f11,axiom,(
% 6.84/1.26    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 6.84/1.26  fof(f36,plain,(
% 6.84/1.26    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.84/1.26    inference(cnf_transformation,[],[f10])).
% 6.84/1.26  fof(f10,axiom,(
% 6.84/1.26    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 6.84/1.26  fof(f40,plain,(
% 6.84/1.26    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.84/1.26    inference(cnf_transformation,[],[f5])).
% 6.84/1.26  fof(f5,axiom,(
% 6.84/1.26    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.84/1.26  fof(f58,plain,(
% 6.84/1.26    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 6.84/1.26    inference(cnf_transformation,[],[f32])).
% 6.84/1.26  fof(f32,plain,(
% 6.84/1.26    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 6.84/1.26    inference(flattening,[],[f31])).
% 6.84/1.26  fof(f31,plain,(
% 6.84/1.26    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 6.84/1.26    inference(nnf_transformation,[],[f16])).
% 6.84/1.26  fof(f16,axiom,(
% 6.84/1.26    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 6.84/1.26  fof(f228,plain,(
% 6.84/1.26    r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~spl3_7),
% 6.84/1.26    inference(avatar_component_clause,[],[f226])).
% 6.84/1.26  fof(f2098,plain,(
% 6.84/1.26    ~spl3_6 | spl3_25),
% 6.84/1.26    inference(avatar_contradiction_clause,[],[f2097])).
% 6.84/1.26  fof(f2097,plain,(
% 6.84/1.26    $false | (~spl3_6 | spl3_25)),
% 6.84/1.26    inference(subsumption_resolution,[],[f1003,f2095])).
% 6.84/1.26  fof(f2095,plain,(
% 6.84/1.26    ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k1_xboole_0)) | spl3_25),
% 6.84/1.26    inference(avatar_component_clause,[],[f2093])).
% 6.84/1.26  fof(f2093,plain,(
% 6.84/1.26    spl3_25 <=> r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k1_xboole_0))),
% 6.84/1.26    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 6.84/1.26  fof(f1003,plain,(
% 6.84/1.26    r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k1_xboole_0)) | ~spl3_6),
% 6.84/1.26    inference(unit_resulting_resolution,[],[f206,f383])).
% 6.84/1.26  fof(f383,plain,(
% 6.84/1.26    ( ! [X4] : (~r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X4,k5_xboole_0(sK1,k1_xboole_0))) )),
% 6.84/1.26    inference(superposition,[],[f87,f327])).
% 6.84/1.26  fof(f327,plain,(
% 6.84/1.26    k5_xboole_0(sK1,k1_xboole_0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 6.84/1.26    inference(superposition,[],[f69,f114])).
% 6.84/1.26  fof(f114,plain,(
% 6.84/1.26    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 6.84/1.26    inference(unit_resulting_resolution,[],[f94,f74])).
% 6.84/1.26  fof(f74,plain,(
% 6.84/1.26    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 6.84/1.26    inference(definition_unfolding,[],[f50,f40])).
% 6.84/1.26  fof(f50,plain,(
% 6.84/1.26    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 6.84/1.26    inference(cnf_transformation,[],[f25])).
% 6.84/1.26  fof(f25,plain,(
% 6.84/1.26    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 6.84/1.26    inference(nnf_transformation,[],[f4])).
% 6.84/1.26  fof(f4,axiom,(
% 6.84/1.26    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 6.84/1.26  fof(f94,plain,(
% 6.84/1.26    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 6.84/1.26    inference(unit_resulting_resolution,[],[f33,f72])).
% 6.84/1.26  fof(f72,plain,(
% 6.84/1.26    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.84/1.26    inference(definition_unfolding,[],[f48,f65])).
% 6.84/1.26  fof(f48,plain,(
% 6.84/1.26    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.84/1.26    inference(cnf_transformation,[],[f24])).
% 6.84/1.26  fof(f24,plain,(
% 6.84/1.26    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 6.84/1.26    inference(nnf_transformation,[],[f14])).
% 6.84/1.26  fof(f14,axiom,(
% 6.84/1.26    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 6.84/1.26  fof(f33,plain,(
% 6.84/1.26    r2_hidden(sK0,sK1)),
% 6.84/1.26    inference(cnf_transformation,[],[f21])).
% 6.84/1.26  fof(f21,plain,(
% 6.84/1.26    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 6.84/1.26    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 6.84/1.26  fof(f20,plain,(
% 6.84/1.26    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 6.84/1.26    introduced(choice_axiom,[])).
% 6.84/1.26  fof(f19,plain,(
% 6.84/1.26    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 6.84/1.26    inference(ennf_transformation,[],[f18])).
% 6.84/1.26  fof(f18,negated_conjecture,(
% 6.84/1.26    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 6.84/1.26    inference(negated_conjecture,[],[f17])).
% 6.84/1.26  fof(f17,conjecture,(
% 6.84/1.26    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 6.84/1.26  fof(f69,plain,(
% 6.84/1.26    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 6.84/1.26    inference(definition_unfolding,[],[f41,f64,f40])).
% 6.84/1.26  fof(f64,plain,(
% 6.84/1.26    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 6.84/1.26    inference(definition_unfolding,[],[f38,f63])).
% 6.84/1.26  fof(f38,plain,(
% 6.84/1.26    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.84/1.26    inference(cnf_transformation,[],[f15])).
% 6.84/1.26  fof(f15,axiom,(
% 6.84/1.26    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 6.84/1.26  fof(f41,plain,(
% 6.84/1.26    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.84/1.26    inference(cnf_transformation,[],[f9])).
% 6.84/1.26  fof(f9,axiom,(
% 6.84/1.26    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 6.84/1.26  fof(f87,plain,(
% 6.84/1.26    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 6.84/1.26    inference(equality_resolution,[],[f79])).
% 6.84/1.26  fof(f79,plain,(
% 6.84/1.26    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 6.84/1.26    inference(definition_unfolding,[],[f54,f64])).
% 6.84/1.26  fof(f54,plain,(
% 6.84/1.26    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 6.84/1.26    inference(cnf_transformation,[],[f30])).
% 6.84/1.26  fof(f30,plain,(
% 6.84/1.26    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.84/1.26    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 6.84/1.26  fof(f29,plain,(
% 6.84/1.26    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 6.84/1.26    introduced(choice_axiom,[])).
% 6.84/1.26  fof(f28,plain,(
% 6.84/1.26    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.84/1.26    inference(rectify,[],[f27])).
% 6.84/1.26  fof(f27,plain,(
% 6.84/1.26    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.84/1.26    inference(flattening,[],[f26])).
% 6.84/1.26  fof(f26,plain,(
% 6.84/1.26    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.84/1.26    inference(nnf_transformation,[],[f2])).
% 6.84/1.26  fof(f2,axiom,(
% 6.84/1.26    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 6.84/1.26  fof(f206,plain,(
% 6.84/1.26    r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl3_6),
% 6.84/1.26    inference(avatar_component_clause,[],[f205])).
% 6.84/1.26  fof(f205,plain,(
% 6.84/1.26    spl3_6 <=> r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 6.84/1.26    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 6.84/1.26  fof(f2096,plain,(
% 6.84/1.26    ~spl3_19 | ~spl3_25 | spl3_5),
% 6.84/1.26    inference(avatar_split_clause,[],[f2087,f201,f2093,f849])).
% 6.84/1.26  fof(f849,plain,(
% 6.84/1.26    spl3_19 <=> r1_tarski(sK1,sK1)),
% 6.84/1.26    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 6.84/1.26  fof(f2087,plain,(
% 6.84/1.26    ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k1_xboole_0)) | ~r1_tarski(sK1,sK1) | spl3_5),
% 6.84/1.26    inference(superposition,[],[f979,f74])).
% 6.84/1.26  fof(f979,plain,(
% 6.84/1.26    ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)))) | spl3_5),
% 6.84/1.26    inference(forward_demodulation,[],[f973,f69])).
% 6.84/1.26  fof(f973,plain,(
% 6.84/1.26    ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl3_5),
% 6.84/1.26    inference(unit_resulting_resolution,[],[f203,f203,f89])).
% 6.84/1.26  fof(f89,plain,(
% 6.84/1.26    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 6.84/1.26    inference(equality_resolution,[],[f81])).
% 6.84/1.26  fof(f81,plain,(
% 6.84/1.26    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 6.84/1.26    inference(definition_unfolding,[],[f52,f64])).
% 6.84/1.26  fof(f52,plain,(
% 6.84/1.26    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 6.84/1.26    inference(cnf_transformation,[],[f30])).
% 6.84/1.26  fof(f203,plain,(
% 6.84/1.26    ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1) | spl3_5),
% 6.84/1.26    inference(avatar_component_clause,[],[f201])).
% 6.84/1.26  fof(f952,plain,(
% 6.84/1.26    ~spl3_5 | spl3_6 | spl3_7),
% 6.84/1.26    inference(avatar_contradiction_clause,[],[f951])).
% 6.84/1.26  fof(f951,plain,(
% 6.84/1.26    $false | (~spl3_5 | spl3_6 | spl3_7)),
% 6.84/1.26    inference(unit_resulting_resolution,[],[f86,f916,f73])).
% 6.84/1.26  fof(f73,plain,(
% 6.84/1.26    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 6.84/1.26    inference(definition_unfolding,[],[f47,f65])).
% 6.84/1.26  fof(f47,plain,(
% 6.84/1.26    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 6.84/1.26    inference(cnf_transformation,[],[f24])).
% 6.84/1.26  fof(f916,plain,(
% 6.84/1.26    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | (~spl3_5 | spl3_6 | spl3_7)),
% 6.84/1.26    inference(superposition,[],[f207,f453])).
% 6.84/1.26  fof(f453,plain,(
% 6.84/1.26    sK0 = sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | (~spl3_5 | spl3_7)),
% 6.84/1.26    inference(unit_resulting_resolution,[],[f202,f227,f82])).
% 6.84/1.26  fof(f82,plain,(
% 6.84/1.26    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 6.84/1.26    inference(definition_unfolding,[],[f60,f40,f65])).
% 6.84/1.26  fof(f60,plain,(
% 6.84/1.26    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 6.84/1.26    inference(cnf_transformation,[],[f32])).
% 6.84/1.26  fof(f227,plain,(
% 6.84/1.26    ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | spl3_7),
% 6.84/1.26    inference(avatar_component_clause,[],[f226])).
% 6.84/1.26  fof(f202,plain,(
% 6.84/1.26    r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1) | ~spl3_5),
% 6.84/1.26    inference(avatar_component_clause,[],[f201])).
% 6.84/1.26  fof(f207,plain,(
% 6.84/1.26    ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl3_6),
% 6.84/1.26    inference(avatar_component_clause,[],[f205])).
% 6.84/1.26  fof(f86,plain,(
% 6.84/1.26    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.84/1.26    inference(equality_resolution,[],[f44])).
% 6.84/1.26  fof(f44,plain,(
% 6.84/1.26    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.84/1.26    inference(cnf_transformation,[],[f23])).
% 6.84/1.26  fof(f23,plain,(
% 6.84/1.26    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.84/1.26    inference(flattening,[],[f22])).
% 6.84/1.26  fof(f22,plain,(
% 6.84/1.26    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.84/1.26    inference(nnf_transformation,[],[f3])).
% 6.84/1.26  fof(f3,axiom,(
% 6.84/1.26    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.84/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.84/1.26  fof(f876,plain,(
% 6.84/1.26    spl3_19),
% 6.84/1.26    inference(avatar_contradiction_clause,[],[f874])).
% 6.84/1.26  fof(f874,plain,(
% 6.84/1.26    $false | spl3_19),
% 6.84/1.26    inference(unit_resulting_resolution,[],[f86,f851])).
% 6.84/1.26  fof(f851,plain,(
% 6.84/1.26    ~r1_tarski(sK1,sK1) | spl3_19),
% 6.84/1.26    inference(avatar_component_clause,[],[f849])).
% 6.84/1.26  fof(f230,plain,(
% 6.84/1.26    ~spl3_5 | ~spl3_7),
% 6.84/1.26    inference(avatar_split_clause,[],[f217,f226,f201])).
% 6.84/1.26  fof(f217,plain,(
% 6.84/1.26    ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1)),
% 6.84/1.26    inference(equality_resolution,[],[f102])).
% 6.84/1.26  fof(f102,plain,(
% 6.84/1.26    ( ! [X1] : (sK1 != X1 | ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X1),X1)) )),
% 6.84/1.26    inference(superposition,[],[f66,f77])).
% 6.84/1.26  fof(f77,plain,(
% 6.84/1.26    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 6.84/1.26    inference(definition_unfolding,[],[f56,f64])).
% 6.84/1.26  fof(f56,plain,(
% 6.84/1.26    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 6.84/1.26    inference(cnf_transformation,[],[f30])).
% 6.84/1.26  fof(f66,plain,(
% 6.84/1.26    sK1 != k3_tarski(k3_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 6.84/1.26    inference(definition_unfolding,[],[f34,f64,f40,f65,f65])).
% 6.84/1.26  fof(f34,plain,(
% 6.84/1.26    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 6.84/1.26    inference(cnf_transformation,[],[f21])).
% 6.84/1.26  fof(f229,plain,(
% 6.84/1.26    spl3_5 | spl3_7 | spl3_6),
% 6.84/1.26    inference(avatar_split_clause,[],[f224,f205,f226,f201])).
% 6.84/1.26  fof(f224,plain,(
% 6.84/1.26    r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1)),
% 6.84/1.26    inference(equality_resolution,[],[f103])).
% 6.84/1.26  fof(f103,plain,(
% 6.84/1.26    ( ! [X2] : (sK1 != X2 | r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X2),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X2),X2)) )),
% 6.84/1.26    inference(superposition,[],[f66,f78])).
% 6.84/1.26  fof(f78,plain,(
% 6.84/1.26    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 6.84/1.26    inference(definition_unfolding,[],[f55,f64])).
% 6.84/1.26  fof(f55,plain,(
% 6.84/1.26    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 6.84/1.26    inference(cnf_transformation,[],[f30])).
% 6.84/1.26  fof(f208,plain,(
% 6.84/1.26    ~spl3_5 | ~spl3_6),
% 6.84/1.26    inference(avatar_split_clause,[],[f199,f205,f201])).
% 6.84/1.26  fof(f199,plain,(
% 6.84/1.26    ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1)),
% 6.84/1.26    inference(equality_resolution,[],[f101])).
% 6.84/1.26  fof(f101,plain,(
% 6.84/1.26    ( ! [X0] : (sK1 != X0 | ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK2(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0),X0)) )),
% 6.84/1.26    inference(superposition,[],[f66,f76])).
% 6.84/1.26  fof(f76,plain,(
% 6.84/1.26    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 6.84/1.26    inference(definition_unfolding,[],[f57,f64])).
% 6.84/1.26  fof(f57,plain,(
% 6.84/1.26    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 6.84/1.26    inference(cnf_transformation,[],[f30])).
% 6.84/1.26  % SZS output end Proof for theBenchmark
% 6.84/1.26  % (27170)------------------------------
% 6.84/1.26  % (27170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.84/1.26  % (27170)Termination reason: Refutation
% 6.84/1.26  
% 6.84/1.26  % (27170)Memory used [KB]: 12920
% 6.84/1.26  % (27170)Time elapsed: 0.366 s
% 6.84/1.26  % (27170)------------------------------
% 6.84/1.26  % (27170)------------------------------
% 6.84/1.27  % (27067)Success in time 0.905 s
%------------------------------------------------------------------------------
