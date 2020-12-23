%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:41 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 172 expanded)
%              Number of leaves         :   16 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  332 ( 806 expanded)
%              Number of equality atoms :  119 ( 172 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1223,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f133,f778,f1222])).

fof(f1222,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f1221])).

fof(f1221,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f1187,f131])).

fof(f131,plain,
    ( r2_hidden(sK4,sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_2
  <=> r2_hidden(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1187,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ spl8_1 ),
    inference(resolution,[],[f789,f200])).

fof(f200,plain,(
    ! [X6,X8,X7] : r2_hidden(X6,k3_enumset1(X7,X7,X7,X8,X6)) ),
    inference(resolution,[],[f123,f120])).

fof(f120,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP2(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
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
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f52,f53])).

fof(f53,plain,(
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

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
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
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP2(X2,X1,X0,X3)
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
        | ~ sP2(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP2(X2,X1,X0,X3)
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
        | ~ sP2(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X2,X1,X0,X3] :
      ( sP2(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f123,plain,(
    ! [X2,X0,X1] : sP2(X2,X1,X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X2,X1,X0,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f102,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f72,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP2(X2,X1,X0,X3) )
      & ( sP2(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP2(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f23,f28])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f789,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
        | ~ r2_hidden(X2,sK3) )
    | ~ spl8_1 ),
    inference(superposition,[],[f189,f126])).

fof(f126,plain,
    ( sK3 = k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_1
  <=> sK3 = k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f82,f119])).

fof(f119,plain,(
    ! [X0,X1] : sP1(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
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
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f45,f46])).

fof(f46,plain,(
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

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
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
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f778,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f777])).

fof(f777,plain,
    ( $false
    | spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f776,f127])).

fof(f127,plain,
    ( sK3 != k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f776,plain,
    ( sK3 = k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | spl8_2 ),
    inference(resolution,[],[f772,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1,X0,X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f772,plain,
    ( sP1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3,sK3)
    | spl8_2 ),
    inference(superposition,[],[f751,f580])).

fof(f580,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3)
    | spl8_2 ),
    inference(resolution,[],[f221,f130])).

fof(f130,plain,
    ( ~ r2_hidden(sK4,sK3)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f221,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(resolution,[],[f110,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f106])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f105])).

fof(f105,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f104])).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f751,plain,(
    ! [X4,X5] : sP1(k4_xboole_0(X4,X5),X5,X5) ),
    inference(duplicate_literal_removal,[],[f735])).

fof(f735,plain,(
    ! [X4,X5] :
      ( sP1(k4_xboole_0(X4,X5),X5,X5)
      | sP1(k4_xboole_0(X4,X5),X5,X5) ) ),
    inference(resolution,[],[f522,f373])).

fof(f373,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,X1),X1)
      | sP1(X0,X1,X1) ) ),
    inference(factoring,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f522,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK6(k4_xboole_0(X6,X7),X8,X8),X7)
      | sP1(k4_xboole_0(X6,X7),X8,X8) ) ),
    inference(resolution,[],[f480,f189])).

fof(f480,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK6(X1,X2,X2),X1)
      | sP1(X1,X2,X2) ) ),
    inference(subsumption_resolution,[],[f478,f84])).

fof(f478,plain,(
    ! [X2,X1] :
      ( sP1(X1,X2,X2)
      | r2_hidden(sK6(X1,X2,X2),X1)
      | ~ r2_hidden(sK6(X1,X2,X2),X2) ) ),
    inference(duplicate_literal_removal,[],[f470])).

fof(f470,plain,(
    ! [X2,X1] :
      ( sP1(X1,X2,X2)
      | r2_hidden(sK6(X1,X2,X2),X1)
      | ~ r2_hidden(sK6(X1,X2,X2),X2)
      | sP1(X1,X2,X2) ) ),
    inference(resolution,[],[f373,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f133,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f109,f129,f125])).

fof(f109,plain,
    ( ~ r2_hidden(sK4,sK3)
    | sK3 = k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f56,f106])).

fof(f56,plain,
    ( ~ r2_hidden(sK4,sK3)
    | sK3 = k4_xboole_0(sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( r2_hidden(sK4,sK3)
      | sK3 != k4_xboole_0(sK3,k1_tarski(sK4)) )
    & ( ~ r2_hidden(sK4,sK3)
      | sK3 = k4_xboole_0(sK3,k1_tarski(sK4)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK4,sK3)
        | sK3 != k4_xboole_0(sK3,k1_tarski(sK4)) )
      & ( ~ r2_hidden(sK4,sK3)
        | sK3 = k4_xboole_0(sK3,k1_tarski(sK4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f132,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f108,f129,f125])).

fof(f108,plain,
    ( r2_hidden(sK4,sK3)
    | sK3 != k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f57,f106])).

fof(f57,plain,
    ( r2_hidden(sK4,sK3)
    | sK3 != k4_xboole_0(sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:10:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (18332)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.22/0.52  % (18324)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.22/0.52  % (18316)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.22/0.52  % (18316)Refutation not found, incomplete strategy% (18316)------------------------------
% 1.22/0.52  % (18316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (18332)Refutation not found, incomplete strategy% (18332)------------------------------
% 1.22/0.52  % (18332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (18332)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (18332)Memory used [KB]: 6268
% 1.22/0.52  % (18332)Time elapsed: 0.116 s
% 1.22/0.52  % (18332)------------------------------
% 1.22/0.52  % (18332)------------------------------
% 1.22/0.52  % (18316)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (18316)Memory used [KB]: 10746
% 1.22/0.52  % (18316)Time elapsed: 0.120 s
% 1.22/0.52  % (18316)------------------------------
% 1.22/0.52  % (18316)------------------------------
% 1.22/0.53  % (18326)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.22/0.53  % (18315)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.35/0.53  % (18320)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.35/0.53  % (18334)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.53  % (18312)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.53  % (18309)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.35/0.53  % (18320)Refutation not found, incomplete strategy% (18320)------------------------------
% 1.35/0.53  % (18320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (18327)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.35/0.54  % (18320)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (18320)Memory used [KB]: 1663
% 1.35/0.54  % (18320)Time elapsed: 0.114 s
% 1.35/0.54  % (18318)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.35/0.54  % (18320)------------------------------
% 1.35/0.54  % (18320)------------------------------
% 1.35/0.54  % (18308)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.35/0.54  % (18310)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.35/0.54  % (18335)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.35/0.54  % (18335)Refutation not found, incomplete strategy% (18335)------------------------------
% 1.35/0.54  % (18335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (18335)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (18335)Memory used [KB]: 1663
% 1.35/0.54  % (18335)Time elapsed: 0.002 s
% 1.35/0.54  % (18335)------------------------------
% 1.35/0.54  % (18335)------------------------------
% 1.35/0.54  % (18333)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.35/0.54  % (18328)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.35/0.54  % (18319)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.35/0.55  % (18307)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.35/0.55  % (18307)Refutation not found, incomplete strategy% (18307)------------------------------
% 1.35/0.55  % (18307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (18307)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (18307)Memory used [KB]: 1663
% 1.35/0.55  % (18307)Time elapsed: 0.134 s
% 1.35/0.55  % (18307)------------------------------
% 1.35/0.55  % (18307)------------------------------
% 1.35/0.55  % (18311)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.35/0.55  % (18325)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.35/0.55  % (18323)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.35/0.55  % (18329)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.35/0.55  % (18323)Refutation not found, incomplete strategy% (18323)------------------------------
% 1.35/0.55  % (18323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (18323)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (18323)Memory used [KB]: 1791
% 1.35/0.55  % (18323)Time elapsed: 0.141 s
% 1.35/0.55  % (18323)------------------------------
% 1.35/0.55  % (18323)------------------------------
% 1.35/0.56  % (18317)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.35/0.56  % (18317)Refutation not found, incomplete strategy% (18317)------------------------------
% 1.35/0.56  % (18317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (18317)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (18317)Memory used [KB]: 6268
% 1.35/0.56  % (18317)Time elapsed: 0.149 s
% 1.35/0.56  % (18317)------------------------------
% 1.35/0.56  % (18317)------------------------------
% 1.35/0.56  % (18321)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.35/0.56  % (18314)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.35/0.56  % (18313)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.35/0.56  % (18331)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.35/0.56  % (18306)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.35/0.57  % (18330)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.35/0.58  % (18322)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.35/0.58  % (18322)Refutation not found, incomplete strategy% (18322)------------------------------
% 1.35/0.58  % (18322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.58  % (18322)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.58  
% 1.35/0.58  % (18322)Memory used [KB]: 10618
% 1.35/0.58  % (18322)Time elapsed: 0.168 s
% 1.35/0.58  % (18322)------------------------------
% 1.35/0.58  % (18322)------------------------------
% 1.98/0.63  % (18312)Refutation found. Thanks to Tanya!
% 1.98/0.63  % SZS status Theorem for theBenchmark
% 1.98/0.63  % SZS output start Proof for theBenchmark
% 1.98/0.63  fof(f1223,plain,(
% 1.98/0.63    $false),
% 1.98/0.63    inference(avatar_sat_refutation,[],[f132,f133,f778,f1222])).
% 1.98/0.63  fof(f1222,plain,(
% 1.98/0.63    ~spl8_1 | ~spl8_2),
% 1.98/0.63    inference(avatar_contradiction_clause,[],[f1221])).
% 1.98/0.63  fof(f1221,plain,(
% 1.98/0.63    $false | (~spl8_1 | ~spl8_2)),
% 1.98/0.63    inference(subsumption_resolution,[],[f1187,f131])).
% 1.98/0.63  fof(f131,plain,(
% 1.98/0.63    r2_hidden(sK4,sK3) | ~spl8_2),
% 1.98/0.63    inference(avatar_component_clause,[],[f129])).
% 1.98/0.63  fof(f129,plain,(
% 1.98/0.63    spl8_2 <=> r2_hidden(sK4,sK3)),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.98/0.63  fof(f1187,plain,(
% 1.98/0.63    ~r2_hidden(sK4,sK3) | ~spl8_1),
% 1.98/0.63    inference(resolution,[],[f789,f200])).
% 1.98/0.63  fof(f200,plain,(
% 1.98/0.63    ( ! [X6,X8,X7] : (r2_hidden(X6,k3_enumset1(X7,X7,X7,X8,X6))) )),
% 1.98/0.63    inference(resolution,[],[f123,f120])).
% 1.98/0.63  fof(f120,plain,(
% 1.98/0.63    ( ! [X2,X5,X3,X1] : (~sP2(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 1.98/0.63    inference(equality_resolution,[],[f97])).
% 1.98/0.63  fof(f97,plain,(
% 1.98/0.63    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP2(X0,X1,X2,X3)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f54])).
% 1.98/0.63  fof(f54,plain,(
% 1.98/0.63    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP2(X0,X1,X2,X3)))),
% 1.98/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f52,f53])).
% 1.98/0.63  fof(f53,plain,(
% 1.98/0.63    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 1.98/0.63    introduced(choice_axiom,[])).
% 1.98/0.63  fof(f52,plain,(
% 1.98/0.63    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP2(X0,X1,X2,X3)))),
% 1.98/0.63    inference(rectify,[],[f51])).
% 1.98/0.63  fof(f51,plain,(
% 1.98/0.63    ! [X2,X1,X0,X3] : ((sP2(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP2(X2,X1,X0,X3)))),
% 1.98/0.63    inference(flattening,[],[f50])).
% 1.98/0.63  fof(f50,plain,(
% 1.98/0.63    ! [X2,X1,X0,X3] : ((sP2(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP2(X2,X1,X0,X3)))),
% 1.98/0.63    inference(nnf_transformation,[],[f28])).
% 1.98/0.63  fof(f28,plain,(
% 1.98/0.63    ! [X2,X1,X0,X3] : (sP2(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.98/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.98/0.63  fof(f123,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (sP2(X2,X1,X0,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 1.98/0.63    inference(equality_resolution,[],[f115])).
% 1.98/0.63  fof(f115,plain,(
% 1.98/0.63    ( ! [X2,X0,X3,X1] : (sP2(X2,X1,X0,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.98/0.63    inference(definition_unfolding,[],[f102,f104])).
% 1.98/0.63  fof(f104,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.98/0.63    inference(definition_unfolding,[],[f72,f93])).
% 1.98/0.63  fof(f93,plain,(
% 1.98/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f15])).
% 1.98/0.63  fof(f15,axiom,(
% 1.98/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.98/0.63  fof(f72,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f14])).
% 1.98/0.63  fof(f14,axiom,(
% 1.98/0.63    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.98/0.64  fof(f102,plain,(
% 1.98/0.64    ( ! [X2,X0,X3,X1] : (sP2(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.98/0.64    inference(cnf_transformation,[],[f55])).
% 1.98/0.64  fof(f55,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP2(X2,X1,X0,X3)) & (sP2(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.98/0.64    inference(nnf_transformation,[],[f29])).
% 1.98/0.64  fof(f29,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP2(X2,X1,X0,X3))),
% 1.98/0.64    inference(definition_folding,[],[f23,f28])).
% 1.98/0.64  fof(f23,plain,(
% 1.98/0.64    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.98/0.64    inference(ennf_transformation,[],[f11])).
% 1.98/0.64  fof(f11,axiom,(
% 1.98/0.64    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.98/0.64  fof(f789,plain,(
% 1.98/0.64    ( ! [X2] : (~r2_hidden(X2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | ~r2_hidden(X2,sK3)) ) | ~spl8_1),
% 1.98/0.64    inference(superposition,[],[f189,f126])).
% 1.98/0.64  fof(f126,plain,(
% 1.98/0.64    sK3 = k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | ~spl8_1),
% 1.98/0.64    inference(avatar_component_clause,[],[f125])).
% 1.98/0.64  fof(f125,plain,(
% 1.98/0.64    spl8_1 <=> sK3 = k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 1.98/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.98/0.64  fof(f189,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 1.98/0.64    inference(resolution,[],[f82,f119])).
% 1.98/0.64  fof(f119,plain,(
% 1.98/0.64    ( ! [X0,X1] : (sP1(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.98/0.64    inference(equality_resolution,[],[f87])).
% 1.98/0.64  fof(f87,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.98/0.64    inference(cnf_transformation,[],[f48])).
% 1.98/0.64  fof(f48,plain,(
% 1.98/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.98/0.64    inference(nnf_transformation,[],[f27])).
% 1.98/0.64  fof(f27,plain,(
% 1.98/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.98/0.64    inference(definition_folding,[],[f2,f26])).
% 1.98/0.64  fof(f26,plain,(
% 1.98/0.64    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.98/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.98/0.64  fof(f2,axiom,(
% 1.98/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.98/0.64  fof(f82,plain,(
% 1.98/0.64    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f47])).
% 1.98/0.64  fof(f47,plain,(
% 1.98/0.64    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.98/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f45,f46])).
% 1.98/0.64  fof(f46,plain,(
% 1.98/0.64    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.98/0.64    introduced(choice_axiom,[])).
% 1.98/0.64  fof(f45,plain,(
% 1.98/0.64    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.98/0.64    inference(rectify,[],[f44])).
% 1.98/0.64  fof(f44,plain,(
% 1.98/0.64    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.98/0.64    inference(flattening,[],[f43])).
% 1.98/0.64  fof(f43,plain,(
% 1.98/0.64    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.98/0.64    inference(nnf_transformation,[],[f26])).
% 1.98/0.64  fof(f778,plain,(
% 1.98/0.64    spl8_1 | spl8_2),
% 1.98/0.64    inference(avatar_contradiction_clause,[],[f777])).
% 1.98/0.64  fof(f777,plain,(
% 1.98/0.64    $false | (spl8_1 | spl8_2)),
% 1.98/0.64    inference(subsumption_resolution,[],[f776,f127])).
% 1.98/0.64  fof(f127,plain,(
% 1.98/0.64    sK3 != k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | spl8_1),
% 1.98/0.64    inference(avatar_component_clause,[],[f125])).
% 1.98/0.64  fof(f776,plain,(
% 1.98/0.64    sK3 = k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | spl8_2),
% 1.98/0.64    inference(resolution,[],[f772,f88])).
% 1.98/0.64  fof(f88,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (~sP1(X1,X0,X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.98/0.64    inference(cnf_transformation,[],[f48])).
% 1.98/0.64  fof(f772,plain,(
% 1.98/0.64    sP1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3,sK3) | spl8_2),
% 1.98/0.64    inference(superposition,[],[f751,f580])).
% 1.98/0.64  fof(f580,plain,(
% 1.98/0.64    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) | spl8_2),
% 1.98/0.64    inference(resolution,[],[f221,f130])).
% 1.98/0.64  fof(f130,plain,(
% 1.98/0.64    ~r2_hidden(sK4,sK3) | spl8_2),
% 1.98/0.64    inference(avatar_component_clause,[],[f129])).
% 1.98/0.64  fof(f221,plain,(
% 1.98/0.64    ( ! [X0,X1] : (r2_hidden(X0,X1) | k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 1.98/0.64    inference(resolution,[],[f110,f68])).
% 1.98/0.64  fof(f68,plain,(
% 1.98/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.98/0.64    inference(cnf_transformation,[],[f35])).
% 1.98/0.64  fof(f35,plain,(
% 1.98/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.98/0.64    inference(nnf_transformation,[],[f10])).
% 1.98/0.64  fof(f10,axiom,(
% 1.98/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.98/0.64  fof(f110,plain,(
% 1.98/0.64    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.98/0.64    inference(definition_unfolding,[],[f63,f106])).
% 1.98/0.64  fof(f106,plain,(
% 1.98/0.64    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.98/0.64    inference(definition_unfolding,[],[f59,f105])).
% 1.98/0.64  fof(f105,plain,(
% 1.98/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.98/0.64    inference(definition_unfolding,[],[f60,f104])).
% 1.98/0.64  fof(f60,plain,(
% 1.98/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f13])).
% 1.98/0.64  fof(f13,axiom,(
% 1.98/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.98/0.64  fof(f59,plain,(
% 1.98/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f12])).
% 1.98/0.64  fof(f12,axiom,(
% 1.98/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.98/0.64  fof(f63,plain,(
% 1.98/0.64    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f20])).
% 1.98/0.64  fof(f20,plain,(
% 1.98/0.64    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.98/0.64    inference(ennf_transformation,[],[f16])).
% 1.98/0.64  fof(f16,axiom,(
% 1.98/0.64    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.98/0.64  fof(f751,plain,(
% 1.98/0.64    ( ! [X4,X5] : (sP1(k4_xboole_0(X4,X5),X5,X5)) )),
% 1.98/0.64    inference(duplicate_literal_removal,[],[f735])).
% 1.98/0.64  fof(f735,plain,(
% 1.98/0.64    ( ! [X4,X5] : (sP1(k4_xboole_0(X4,X5),X5,X5) | sP1(k4_xboole_0(X4,X5),X5,X5)) )),
% 1.98/0.64    inference(resolution,[],[f522,f373])).
% 1.98/0.64  fof(f373,plain,(
% 1.98/0.64    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1,X1),X1) | sP1(X0,X1,X1)) )),
% 1.98/0.64    inference(factoring,[],[f84])).
% 1.98/0.64  fof(f84,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X1) | sP1(X0,X1,X2)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f47])).
% 1.98/0.64  fof(f522,plain,(
% 1.98/0.64    ( ! [X6,X8,X7] : (~r2_hidden(sK6(k4_xboole_0(X6,X7),X8,X8),X7) | sP1(k4_xboole_0(X6,X7),X8,X8)) )),
% 1.98/0.64    inference(resolution,[],[f480,f189])).
% 1.98/0.64  fof(f480,plain,(
% 1.98/0.64    ( ! [X2,X1] : (r2_hidden(sK6(X1,X2,X2),X1) | sP1(X1,X2,X2)) )),
% 1.98/0.64    inference(subsumption_resolution,[],[f478,f84])).
% 1.98/0.64  fof(f478,plain,(
% 1.98/0.64    ( ! [X2,X1] : (sP1(X1,X2,X2) | r2_hidden(sK6(X1,X2,X2),X1) | ~r2_hidden(sK6(X1,X2,X2),X2)) )),
% 1.98/0.64    inference(duplicate_literal_removal,[],[f470])).
% 1.98/0.64  fof(f470,plain,(
% 1.98/0.64    ( ! [X2,X1] : (sP1(X1,X2,X2) | r2_hidden(sK6(X1,X2,X2),X1) | ~r2_hidden(sK6(X1,X2,X2),X2) | sP1(X1,X2,X2)) )),
% 1.98/0.64    inference(resolution,[],[f373,f86])).
% 1.98/0.64  fof(f86,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | sP1(X0,X1,X2)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f47])).
% 1.98/0.64  fof(f133,plain,(
% 1.98/0.64    spl8_1 | ~spl8_2),
% 1.98/0.64    inference(avatar_split_clause,[],[f109,f129,f125])).
% 1.98/0.64  fof(f109,plain,(
% 1.98/0.64    ~r2_hidden(sK4,sK3) | sK3 = k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 1.98/0.64    inference(definition_unfolding,[],[f56,f106])).
% 1.98/0.64  fof(f56,plain,(
% 1.98/0.64    ~r2_hidden(sK4,sK3) | sK3 = k4_xboole_0(sK3,k1_tarski(sK4))),
% 1.98/0.64    inference(cnf_transformation,[],[f32])).
% 1.98/0.64  fof(f32,plain,(
% 1.98/0.64    (r2_hidden(sK4,sK3) | sK3 != k4_xboole_0(sK3,k1_tarski(sK4))) & (~r2_hidden(sK4,sK3) | sK3 = k4_xboole_0(sK3,k1_tarski(sK4)))),
% 1.98/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f31])).
% 1.98/0.64  fof(f31,plain,(
% 1.98/0.64    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK4,sK3) | sK3 != k4_xboole_0(sK3,k1_tarski(sK4))) & (~r2_hidden(sK4,sK3) | sK3 = k4_xboole_0(sK3,k1_tarski(sK4))))),
% 1.98/0.64    introduced(choice_axiom,[])).
% 1.98/0.64  fof(f30,plain,(
% 1.98/0.64    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.98/0.64    inference(nnf_transformation,[],[f19])).
% 1.98/0.64  fof(f19,plain,(
% 1.98/0.64    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.98/0.64    inference(ennf_transformation,[],[f18])).
% 1.98/0.64  fof(f18,negated_conjecture,(
% 1.98/0.64    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.98/0.64    inference(negated_conjecture,[],[f17])).
% 1.98/0.64  fof(f17,conjecture,(
% 1.98/0.64    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.98/0.64  fof(f132,plain,(
% 1.98/0.64    ~spl8_1 | spl8_2),
% 1.98/0.64    inference(avatar_split_clause,[],[f108,f129,f125])).
% 1.98/0.64  fof(f108,plain,(
% 1.98/0.64    r2_hidden(sK4,sK3) | sK3 != k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 1.98/0.64    inference(definition_unfolding,[],[f57,f106])).
% 1.98/0.64  fof(f57,plain,(
% 1.98/0.64    r2_hidden(sK4,sK3) | sK3 != k4_xboole_0(sK3,k1_tarski(sK4))),
% 1.98/0.64    inference(cnf_transformation,[],[f32])).
% 1.98/0.64  % SZS output end Proof for theBenchmark
% 1.98/0.64  % (18312)------------------------------
% 1.98/0.64  % (18312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.64  % (18312)Termination reason: Refutation
% 1.98/0.64  
% 1.98/0.64  % (18312)Memory used [KB]: 11641
% 1.98/0.64  % (18312)Time elapsed: 0.214 s
% 1.98/0.64  % (18312)------------------------------
% 1.98/0.64  % (18312)------------------------------
% 1.98/0.65  % (18305)Success in time 0.278 s
%------------------------------------------------------------------------------
