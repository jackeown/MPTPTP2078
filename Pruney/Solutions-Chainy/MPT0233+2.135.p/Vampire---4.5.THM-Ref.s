%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 207 expanded)
%              Number of leaves         :   24 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :  406 ( 907 expanded)
%              Number of equality atoms :  194 ( 497 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f102,f136,f147,f157,f172,f178,f185,f186,f196,f203])).

fof(f203,plain,
    ( spl7_1
    | spl7_8
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl7_1
    | spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f171,f91,f91,f195,f82])).

fof(f82,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f35,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f20])).

% (21398)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f195,plain,
    ( r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK1))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl7_10
  <=> r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f91,plain,
    ( sK0 != sK2
    | spl7_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f171,plain,
    ( sK0 != sK1
    | spl7_8 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl7_8
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f196,plain,
    ( spl7_10
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f190,f150,f143,f193])).

fof(f143,plain,
    ( spl7_5
  <=> r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f150,plain,
    ( spl7_6
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f190,plain,
    ( r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK1))
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f145,f152])).

fof(f152,plain,
    ( sK1 = sK3
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f145,plain,
    ( r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f186,plain,
    ( sK0 != sK1
    | sK1 != sK3
    | sK0 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f185,plain,
    ( spl7_2
    | spl7_8
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl7_2
    | spl7_8
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f96,f171,f171,f177,f82])).

fof(f177,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK3))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl7_9
  <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f96,plain,
    ( sK0 != sK3
    | spl7_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl7_2
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f178,plain,
    ( spl7_9
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f173,f154,f143,f175])).

fof(f154,plain,
    ( spl7_7
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f173,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK3))
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f145,f156])).

fof(f156,plain,
    ( sK1 = sK2
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f172,plain,
    ( ~ spl7_8
    | spl7_1
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f167,f154,f89,f169])).

fof(f167,plain,
    ( sK0 != sK1
    | spl7_1
    | ~ spl7_7 ),
    inference(superposition,[],[f91,f156])).

% (21392)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f157,plain,
    ( spl7_6
    | spl7_7
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f148,f133,f154,f150])).

fof(f133,plain,
    ( spl7_4
  <=> r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f148,plain,
    ( sK1 = sK2
    | sK1 = sK3
    | ~ spl7_4 ),
    inference(resolution,[],[f135,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f135,plain,
    ( r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f147,plain,
    ( spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f129,f99,f143])).

fof(f99,plain,
    ( spl7_3
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f129,plain,
    ( r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl7_3 ),
    inference(resolution,[],[f126,f81])).

fof(f81,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f36,f58])).

fof(f36,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK3)) )
    | ~ spl7_3 ),
    inference(resolution,[],[f125,f101])).

fof(f101,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f125,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X3,X4)
      | r2_hidden(X3,X5) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X4,X5)
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f105,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f105,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(X4,X5))
      | ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f57,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f59,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f136,plain,
    ( spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f127,f99,f133])).

fof(f127,plain,
    ( r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl7_3 ),
    inference(resolution,[],[f126,f77])).

fof(f77,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f58])).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f102,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f61,f99])).

fof(f61,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f32,f60,f60])).

fof(f32,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f97,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f34,f94])).

fof(f34,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f33,f89])).

fof(f33,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

% (21389)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (21386)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.50  % (21402)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (21383)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (21379)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (21387)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (21394)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (21402)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 1.36/0.53  % (21401)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.36/0.53  % (21393)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.36/0.53  % (21395)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.36/0.53  % (21384)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.36/0.53  % (21380)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.36/0.53  % (21405)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.36/0.53  % (21380)Refutation not found, incomplete strategy% (21380)------------------------------
% 1.36/0.53  % (21380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (21380)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (21380)Memory used [KB]: 1663
% 1.36/0.53  % (21380)Time elapsed: 0.126 s
% 1.36/0.53  % (21380)------------------------------
% 1.36/0.53  % (21380)------------------------------
% 1.36/0.54  % (21406)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.36/0.54  % (21405)Refutation not found, incomplete strategy% (21405)------------------------------
% 1.36/0.54  % (21405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (21405)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (21405)Memory used [KB]: 6268
% 1.36/0.54  % (21405)Time elapsed: 0.127 s
% 1.36/0.54  % (21405)------------------------------
% 1.36/0.54  % (21405)------------------------------
% 1.36/0.54  % (21381)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.36/0.54  % (21388)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.36/0.54  % (21395)Refutation not found, incomplete strategy% (21395)------------------------------
% 1.36/0.54  % (21395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (21395)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (21395)Memory used [KB]: 10618
% 1.36/0.54  % (21395)Time elapsed: 0.127 s
% 1.36/0.54  % (21395)------------------------------
% 1.36/0.54  % (21395)------------------------------
% 1.36/0.54  % (21382)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.36/0.54  % (21408)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.36/0.54  % (21385)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.54  % (21408)Refutation not found, incomplete strategy% (21408)------------------------------
% 1.36/0.54  % (21408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (21408)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (21408)Memory used [KB]: 1663
% 1.36/0.54  % (21408)Time elapsed: 0.127 s
% 1.36/0.54  % (21408)------------------------------
% 1.36/0.54  % (21408)------------------------------
% 1.36/0.54  % (21407)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.36/0.54  % (21397)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.36/0.54  % (21400)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.36/0.54  % (21403)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.54  % (21396)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.54  % (21404)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.50/0.55  % (21399)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.55  % SZS output start Proof for theBenchmark
% 1.50/0.55  fof(f204,plain,(
% 1.50/0.55    $false),
% 1.50/0.55    inference(avatar_sat_refutation,[],[f92,f97,f102,f136,f147,f157,f172,f178,f185,f186,f196,f203])).
% 1.50/0.55  fof(f203,plain,(
% 1.50/0.55    spl7_1 | spl7_8 | ~spl7_10),
% 1.50/0.55    inference(avatar_contradiction_clause,[],[f198])).
% 1.50/0.55  fof(f198,plain,(
% 1.50/0.55    $false | (spl7_1 | spl7_8 | ~spl7_10)),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f171,f91,f91,f195,f82])).
% 1.50/0.55  fof(f82,plain,(
% 1.50/0.55    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.50/0.55    inference(equality_resolution,[],[f69])).
% 1.50/0.55  fof(f69,plain,(
% 1.50/0.55    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.50/0.55    inference(definition_unfolding,[],[f35,f58])).
% 1.50/0.55  fof(f58,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f8])).
% 1.50/0.55  fof(f8,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.55  fof(f35,plain,(
% 1.50/0.55    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.50/0.55    inference(cnf_transformation,[],[f23])).
% 1.50/0.55  fof(f23,plain,(
% 1.50/0.55    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.50/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 1.50/0.55  fof(f22,plain,(
% 1.50/0.55    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.50/0.55    introduced(choice_axiom,[])).
% 1.50/0.55  fof(f21,plain,(
% 1.50/0.55    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.50/0.55    inference(rectify,[],[f20])).
% 1.50/0.55  % (21398)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.50/0.55  fof(f20,plain,(
% 1.50/0.55    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.50/0.55    inference(flattening,[],[f19])).
% 1.50/0.55  fof(f19,plain,(
% 1.50/0.55    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.50/0.55    inference(nnf_transformation,[],[f13])).
% 1.50/0.55  fof(f13,plain,(
% 1.50/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.50/0.55    inference(ennf_transformation,[],[f5])).
% 1.50/0.55  fof(f5,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.50/0.55  fof(f195,plain,(
% 1.50/0.55    r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK1)) | ~spl7_10),
% 1.50/0.55    inference(avatar_component_clause,[],[f193])).
% 1.50/0.55  fof(f193,plain,(
% 1.50/0.55    spl7_10 <=> r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK1))),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.50/0.55  fof(f91,plain,(
% 1.50/0.55    sK0 != sK2 | spl7_1),
% 1.50/0.55    inference(avatar_component_clause,[],[f89])).
% 1.50/0.55  fof(f89,plain,(
% 1.50/0.55    spl7_1 <=> sK0 = sK2),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.50/0.55  fof(f171,plain,(
% 1.50/0.55    sK0 != sK1 | spl7_8),
% 1.50/0.55    inference(avatar_component_clause,[],[f169])).
% 1.50/0.55  fof(f169,plain,(
% 1.50/0.55    spl7_8 <=> sK0 = sK1),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.50/0.55  fof(f196,plain,(
% 1.50/0.55    spl7_10 | ~spl7_5 | ~spl7_6),
% 1.50/0.55    inference(avatar_split_clause,[],[f190,f150,f143,f193])).
% 1.50/0.55  fof(f143,plain,(
% 1.50/0.55    spl7_5 <=> r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.50/0.55  fof(f150,plain,(
% 1.50/0.55    spl7_6 <=> sK1 = sK3),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.50/0.55  fof(f190,plain,(
% 1.50/0.55    r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK1)) | (~spl7_5 | ~spl7_6)),
% 1.50/0.55    inference(forward_demodulation,[],[f145,f152])).
% 1.50/0.55  fof(f152,plain,(
% 1.50/0.55    sK1 = sK3 | ~spl7_6),
% 1.50/0.55    inference(avatar_component_clause,[],[f150])).
% 1.50/0.55  fof(f145,plain,(
% 1.50/0.55    r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl7_5),
% 1.50/0.55    inference(avatar_component_clause,[],[f143])).
% 1.50/0.55  fof(f186,plain,(
% 1.50/0.55    sK0 != sK1 | sK1 != sK3 | sK0 = sK3),
% 1.50/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.50/0.55  fof(f185,plain,(
% 1.50/0.55    spl7_2 | spl7_8 | ~spl7_9),
% 1.50/0.55    inference(avatar_contradiction_clause,[],[f180])).
% 1.50/0.55  fof(f180,plain,(
% 1.50/0.55    $false | (spl7_2 | spl7_8 | ~spl7_9)),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f96,f171,f171,f177,f82])).
% 1.50/0.55  fof(f177,plain,(
% 1.50/0.55    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK3)) | ~spl7_9),
% 1.50/0.55    inference(avatar_component_clause,[],[f175])).
% 1.50/0.55  fof(f175,plain,(
% 1.50/0.55    spl7_9 <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK3))),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.50/0.55  fof(f96,plain,(
% 1.50/0.55    sK0 != sK3 | spl7_2),
% 1.50/0.55    inference(avatar_component_clause,[],[f94])).
% 1.50/0.55  fof(f94,plain,(
% 1.50/0.55    spl7_2 <=> sK0 = sK3),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.50/0.55  fof(f178,plain,(
% 1.50/0.55    spl7_9 | ~spl7_5 | ~spl7_7),
% 1.50/0.55    inference(avatar_split_clause,[],[f173,f154,f143,f175])).
% 1.50/0.55  fof(f154,plain,(
% 1.50/0.55    spl7_7 <=> sK1 = sK2),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.50/0.55  fof(f173,plain,(
% 1.50/0.55    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK3)) | (~spl7_5 | ~spl7_7)),
% 1.50/0.55    inference(forward_demodulation,[],[f145,f156])).
% 1.50/0.55  fof(f156,plain,(
% 1.50/0.55    sK1 = sK2 | ~spl7_7),
% 1.50/0.55    inference(avatar_component_clause,[],[f154])).
% 1.50/0.55  fof(f172,plain,(
% 1.50/0.55    ~spl7_8 | spl7_1 | ~spl7_7),
% 1.50/0.55    inference(avatar_split_clause,[],[f167,f154,f89,f169])).
% 1.50/0.55  fof(f167,plain,(
% 1.50/0.55    sK0 != sK1 | (spl7_1 | ~spl7_7)),
% 1.50/0.55    inference(superposition,[],[f91,f156])).
% 1.50/0.55  % (21392)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.55  fof(f157,plain,(
% 1.50/0.55    spl7_6 | spl7_7 | ~spl7_4),
% 1.50/0.55    inference(avatar_split_clause,[],[f148,f133,f154,f150])).
% 1.50/0.55  fof(f133,plain,(
% 1.50/0.55    spl7_4 <=> r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.50/0.55  fof(f148,plain,(
% 1.50/0.55    sK1 = sK2 | sK1 = sK3 | ~spl7_4),
% 1.50/0.55    inference(resolution,[],[f135,f87])).
% 1.50/0.55  fof(f87,plain,(
% 1.50/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.50/0.55    inference(equality_resolution,[],[f75])).
% 1.50/0.55  fof(f75,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.50/0.55    inference(definition_unfolding,[],[f43,f60])).
% 1.50/0.55  fof(f60,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f50,f58])).
% 1.50/0.55  fof(f50,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f7])).
% 1.50/0.55  fof(f7,axiom,(
% 1.50/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.55  fof(f43,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.50/0.55    inference(cnf_transformation,[],[f28])).
% 1.50/0.55  fof(f28,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.50/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 1.50/0.55  fof(f27,plain,(
% 1.50/0.55    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.50/0.55    introduced(choice_axiom,[])).
% 1.50/0.55  fof(f26,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.50/0.55    inference(rectify,[],[f25])).
% 1.50/0.55  fof(f25,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.50/0.55    inference(flattening,[],[f24])).
% 1.50/0.55  fof(f24,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.50/0.55    inference(nnf_transformation,[],[f6])).
% 1.50/0.55  fof(f6,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.50/0.55  fof(f135,plain,(
% 1.50/0.55    r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl7_4),
% 1.50/0.55    inference(avatar_component_clause,[],[f133])).
% 1.50/0.55  fof(f147,plain,(
% 1.50/0.55    spl7_5 | ~spl7_3),
% 1.50/0.55    inference(avatar_split_clause,[],[f129,f99,f143])).
% 1.50/0.55  fof(f99,plain,(
% 1.50/0.55    spl7_3 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.50/0.55  fof(f129,plain,(
% 1.50/0.55    r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl7_3),
% 1.50/0.55    inference(resolution,[],[f126,f81])).
% 1.50/0.55  fof(f81,plain,(
% 1.50/0.55    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 1.50/0.55    inference(equality_resolution,[],[f80])).
% 1.50/0.55  fof(f80,plain,(
% 1.50/0.55    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 1.50/0.55    inference(equality_resolution,[],[f68])).
% 1.50/0.55  fof(f68,plain,(
% 1.50/0.55    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.50/0.55    inference(definition_unfolding,[],[f36,f58])).
% 1.50/0.55  fof(f36,plain,(
% 1.50/0.55    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.50/0.55    inference(cnf_transformation,[],[f23])).
% 1.50/0.55  fof(f126,plain,(
% 1.50/0.55    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK3))) ) | ~spl7_3),
% 1.50/0.55    inference(resolution,[],[f125,f101])).
% 1.50/0.55  fof(f101,plain,(
% 1.50/0.55    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl7_3),
% 1.50/0.55    inference(avatar_component_clause,[],[f99])).
% 1.50/0.55  fof(f125,plain,(
% 1.50/0.55    ( ! [X4,X5,X3] : (~r1_tarski(X4,X5) | ~r2_hidden(X3,X4) | r2_hidden(X3,X5)) )),
% 1.50/0.55    inference(duplicate_literal_removal,[],[f122])).
% 1.50/0.55  fof(f122,plain,(
% 1.50/0.55    ( ! [X4,X5,X3] : (~r2_hidden(X3,X4) | ~r1_tarski(X4,X5) | r2_hidden(X3,X5) | ~r2_hidden(X3,X4)) )),
% 1.50/0.55    inference(resolution,[],[f105,f53])).
% 1.50/0.55  fof(f53,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f29])).
% 1.50/0.55  fof(f29,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.50/0.55    inference(nnf_transformation,[],[f15])).
% 1.50/0.55  fof(f15,plain,(
% 1.50/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.50/0.55    inference(ennf_transformation,[],[f1])).
% 1.50/0.55  fof(f1,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.50/0.55  fof(f105,plain,(
% 1.50/0.55    ( ! [X4,X5,X3] : (~r2_hidden(X3,k5_xboole_0(X4,X5)) | ~r2_hidden(X3,X4) | ~r1_tarski(X4,X5)) )),
% 1.50/0.55    inference(resolution,[],[f57,f103])).
% 1.50/0.55  fof(f103,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 1.50/0.55    inference(superposition,[],[f59,f49])).
% 1.50/0.55  fof(f49,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f14])).
% 1.50/0.55  fof(f14,plain,(
% 1.50/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.50/0.55    inference(ennf_transformation,[],[f4])).
% 1.50/0.55  fof(f4,axiom,(
% 1.50/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.50/0.55  fof(f59,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f3])).
% 1.50/0.55  fof(f3,axiom,(
% 1.50/0.55    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.50/0.55  fof(f57,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f31])).
% 1.50/0.55  fof(f31,plain,(
% 1.50/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.50/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f30])).
% 1.50/0.55  fof(f30,plain,(
% 1.50/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.50/0.55    introduced(choice_axiom,[])).
% 1.50/0.55  fof(f16,plain,(
% 1.50/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.50/0.55    inference(ennf_transformation,[],[f11])).
% 1.50/0.55  fof(f11,plain,(
% 1.50/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.50/0.55    inference(rectify,[],[f2])).
% 1.50/0.55  fof(f2,axiom,(
% 1.50/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.50/0.55  fof(f136,plain,(
% 1.50/0.55    spl7_4 | ~spl7_3),
% 1.50/0.55    inference(avatar_split_clause,[],[f127,f99,f133])).
% 1.50/0.55  fof(f127,plain,(
% 1.50/0.55    r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl7_3),
% 1.50/0.55    inference(resolution,[],[f126,f77])).
% 1.50/0.55  fof(f77,plain,(
% 1.50/0.55    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 1.50/0.55    inference(equality_resolution,[],[f76])).
% 1.50/0.55  fof(f76,plain,(
% 1.50/0.55    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 1.50/0.55    inference(equality_resolution,[],[f66])).
% 1.50/0.55  fof(f66,plain,(
% 1.50/0.55    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.50/0.55    inference(definition_unfolding,[],[f38,f58])).
% 1.50/0.55  fof(f38,plain,(
% 1.50/0.55    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.50/0.55    inference(cnf_transformation,[],[f23])).
% 1.50/0.55  fof(f102,plain,(
% 1.50/0.55    spl7_3),
% 1.50/0.55    inference(avatar_split_clause,[],[f61,f99])).
% 1.50/0.55  fof(f61,plain,(
% 1.50/0.55    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.50/0.55    inference(definition_unfolding,[],[f32,f60,f60])).
% 1.50/0.55  fof(f32,plain,(
% 1.50/0.55    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.50/0.55    inference(cnf_transformation,[],[f18])).
% 1.50/0.55  fof(f18,plain,(
% 1.50/0.55    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.50/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f17])).
% 1.50/0.55  fof(f17,plain,(
% 1.50/0.55    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 1.50/0.55    introduced(choice_axiom,[])).
% 1.50/0.55  fof(f12,plain,(
% 1.50/0.55    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.50/0.55    inference(ennf_transformation,[],[f10])).
% 1.50/0.55  fof(f10,negated_conjecture,(
% 1.50/0.55    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.50/0.55    inference(negated_conjecture,[],[f9])).
% 1.50/0.55  fof(f9,conjecture,(
% 1.50/0.55    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.50/0.55  fof(f97,plain,(
% 1.50/0.55    ~spl7_2),
% 1.50/0.55    inference(avatar_split_clause,[],[f34,f94])).
% 1.50/0.55  fof(f34,plain,(
% 1.50/0.55    sK0 != sK3),
% 1.50/0.55    inference(cnf_transformation,[],[f18])).
% 1.50/0.55  fof(f92,plain,(
% 1.50/0.55    ~spl7_1),
% 1.50/0.55    inference(avatar_split_clause,[],[f33,f89])).
% 1.50/0.55  fof(f33,plain,(
% 1.50/0.55    sK0 != sK2),
% 1.50/0.55    inference(cnf_transformation,[],[f18])).
% 1.50/0.55  % (21389)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.55  % SZS output end Proof for theBenchmark
% 1.50/0.55  % (21402)------------------------------
% 1.50/0.55  % (21402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (21402)Termination reason: Refutation
% 1.50/0.55  
% 1.50/0.55  % (21402)Memory used [KB]: 10874
% 1.50/0.55  % (21402)Time elapsed: 0.113 s
% 1.50/0.55  % (21402)------------------------------
% 1.50/0.55  % (21402)------------------------------
% 1.50/0.55  % (21378)Success in time 0.192 s
%------------------------------------------------------------------------------
