%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 138 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  375 ( 537 expanded)
%              Number of equality atoms :  117 ( 165 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f90,f91,f112,f118,f134,f136])).

fof(f136,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(resolution,[],[f120,f84])).

fof(f84,plain,
    ( ~ r2_hidden(sK2,sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl8_2
  <=> r2_hidden(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f120,plain,
    ( r2_hidden(sK2,sK4)
    | ~ spl8_1 ),
    inference(resolution,[],[f79,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f79,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl8_1
  <=> r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f134,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl8_1
    | spl8_3 ),
    inference(trivial_inequality_removal,[],[f132])).

fof(f132,plain,
    ( sK3 != sK3
    | ~ spl8_1
    | spl8_3 ),
    inference(superposition,[],[f88,f129])).

fof(f129,plain,
    ( sK3 = sK5
    | ~ spl8_1 ),
    inference(resolution,[],[f125,f119])).

fof(f119,plain,
    ( r2_hidden(sK3,k1_enumset1(sK5,sK5,sK5))
    | ~ spl8_1 ),
    inference(resolution,[],[f79,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
      | X0 = X1 ) ),
    inference(condensation,[],[f123])).

fof(f123,plain,(
    ! [X6,X7,X5] :
      ( X5 = X6
      | ~ r2_hidden(X5,X7)
      | ~ r2_hidden(X5,k1_enumset1(X6,X6,X6)) ) ),
    inference(resolution,[],[f68,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f41,f71])).

fof(f71,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f11])).

fof(f11,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f88,plain,
    ( sK3 != sK5
    | spl8_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl8_3
  <=> sK3 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f118,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl8_4 ),
    inference(resolution,[],[f111,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f76,f75])).

fof(f75,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ( sK7(X0,X1,X2,X3) != X0
              & sK7(X0,X1,X2,X3) != X1
              & sK7(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( sK7(X0,X1,X2,X3) = X0
            | sK7(X0,X1,X2,X3) = X1
            | sK7(X0,X1,X2,X3) = X2
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK7(X0,X1,X2,X3) != X0
            & sK7(X0,X1,X2,X3) != X1
            & sK7(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( sK7(X0,X1,X2,X3) = X0
          | sK7(X0,X1,X2,X3) = X1
          | sK7(X0,X1,X2,X3) = X2
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f76,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f10,f13])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f111,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_4
  <=> r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f112,plain,
    ( ~ spl8_2
    | ~ spl8_4
    | spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f105,f86,f78,f109,f82])).

fof(f105,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | ~ r2_hidden(sK2,sK4)
    | spl8_1
    | ~ spl8_3 ),
    inference(resolution,[],[f63,f92])).

fof(f92,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK3,sK3,sK3)))
    | spl8_1
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f80,f87])).

fof(f87,plain,
    ( sK3 = sK5
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f80,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f67,f82,f78])).

fof(f67,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5))) ),
    inference(definition_unfolding,[],[f35,f64])).

fof(f35,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK3 != sK5
      | ~ r2_hidden(sK2,sK4)
      | ~ r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5))) )
    & ( ( sK3 = sK5
        & r2_hidden(sK2,sK4) )
      | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | ~ r2_hidden(X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
        & ( ( X1 = X3
            & r2_hidden(X0,X2) )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) )
   => ( ( sK3 != sK5
        | ~ r2_hidden(sK2,sK4)
        | ~ r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5))) )
      & ( ( sK3 = sK5
          & r2_hidden(sK2,sK4) )
        | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5))) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <~> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      <=> ( X1 = X3
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f90,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f66,f86,f78])).

fof(f66,plain,
    ( sK3 = sK5
    | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5))) ),
    inference(definition_unfolding,[],[f36,f64])).

fof(f36,plain,
    ( sK3 = sK5
    | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f65,f86,f82,f78])).

fof(f65,plain,
    ( sK3 != sK5
    | ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5))) ),
    inference(definition_unfolding,[],[f37,f64])).

fof(f37,plain,
    ( sK3 != sK5
    | ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:46:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (18173)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (18173)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (18181)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f89,f90,f91,f112,f118,f134,f136])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    ~spl8_1 | spl8_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    $false | (~spl8_1 | spl8_2)),
% 0.20/0.47    inference(resolution,[],[f120,f84])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ~r2_hidden(sK2,sK4) | spl8_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl8_2 <=> r2_hidden(sK2,sK4)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    r2_hidden(sK2,sK4) | ~spl8_1),
% 0.20/0.47    inference(resolution,[],[f79,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.47    inference(flattening,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.47    inference(nnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5))) | ~spl8_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f78])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl8_1 <=> r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ~spl8_1 | spl8_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f133])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    $false | (~spl8_1 | spl8_3)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f132])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    sK3 != sK3 | (~spl8_1 | spl8_3)),
% 0.20/0.47    inference(superposition,[],[f88,f129])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    sK3 = sK5 | ~spl8_1),
% 0.20/0.47    inference(resolution,[],[f125,f119])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    r2_hidden(sK3,k1_enumset1(sK5,sK5,sK5)) | ~spl8_1),
% 0.20/0.47    inference(resolution,[],[f79,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1) )),
% 0.20/0.47    inference(condensation,[],[f123])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    ( ! [X6,X7,X5] : (X5 = X6 | ~r2_hidden(X5,X7) | ~r2_hidden(X5,k1_enumset1(X6,X6,X6))) )),
% 0.20/0.47    inference(resolution,[],[f68,f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 0.20/0.47    inference(resolution,[],[f41,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.47    inference(nnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.20/0.47    inference(definition_folding,[],[f1,f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.47    inference(rectify,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.47    inference(nnf_transformation,[],[f11])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f50,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f38,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.47    inference(flattening,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.47    inference(nnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    sK3 != sK5 | spl8_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl8_3 <=> sK3 = sK5),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl8_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    $false | spl8_4),
% 0.20/0.47    inference(resolution,[],[f111,f93])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 0.20/0.47    inference(resolution,[],[f76,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ( ! [X0,X5,X3,X1] : (~sP1(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 0.20/0.47    inference(equality_resolution,[],[f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.20/0.47    inference(rectify,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 0.20/0.47    inference(flattening,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 0.20/0.47    inference(nnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 0.20/0.47    inference(equality_resolution,[],[f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.47    inference(nnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 0.20/0.47    inference(definition_folding,[],[f10,f13])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ~r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | spl8_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f109])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    spl8_4 <=> r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    ~spl8_2 | ~spl8_4 | spl8_1 | ~spl8_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f105,f86,f78,f109,f82])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    ~r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | ~r2_hidden(sK2,sK4) | (spl8_1 | ~spl8_3)),
% 0.20/0.47    inference(resolution,[],[f63,f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ~r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK3,sK3,sK3))) | (spl8_1 | ~spl8_3)),
% 0.20/0.47    inference(forward_demodulation,[],[f80,f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    sK3 = sK5 | ~spl8_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f86])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ~r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5))) | spl8_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f78])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl8_1 | spl8_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f67,f82,f78])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    r2_hidden(sK2,sK4) | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))),
% 0.20/0.47    inference(definition_unfolding,[],[f35,f64])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    r2_hidden(sK2,sK4) | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5)))),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    (sK3 != sK5 | ~r2_hidden(sK2,sK4) | ~r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5)))) & ((sK3 = sK5 & r2_hidden(sK2,sK4)) | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5))))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : ((X1 != X3 | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))))) => ((sK3 != sK5 | ~r2_hidden(sK2,sK4) | ~r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5)))) & ((sK3 = sK5 & r2_hidden(sK2,sK4)) | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5)))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : ((X1 != X3 | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (((X1 != X3 | ~r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.20/0.47    inference(nnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <~> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl8_1 | spl8_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f66,f86,f78])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    sK3 = sK5 | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))),
% 0.20/0.47    inference(definition_unfolding,[],[f36,f64])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    sK3 = sK5 | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5)))),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f65,f86,f82,f78])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    sK3 != sK5 | ~r2_hidden(sK2,sK4) | ~r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))),
% 0.20/0.47    inference(definition_unfolding,[],[f37,f64])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    sK3 != sK5 | ~r2_hidden(sK2,sK4) | ~r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(sK4,k1_tarski(sK5)))),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (18173)------------------------------
% 0.20/0.47  % (18173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (18173)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (18173)Memory used [KB]: 6268
% 0.20/0.47  % (18173)Time elapsed: 0.059 s
% 0.20/0.47  % (18173)------------------------------
% 0.20/0.47  % (18173)------------------------------
% 0.20/0.47  % (18160)Success in time 0.119 s
%------------------------------------------------------------------------------
