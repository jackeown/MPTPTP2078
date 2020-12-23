%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:43 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 152 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  307 ( 528 expanded)
%              Number of equality atoms :  147 ( 189 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f361,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f90,f103,f325,f334,f360])).

fof(f360,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f88,f76,f101,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f101,plain,
    ( r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_3
  <=> r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f76,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f33,f51])).

% (11373)Refutation not found, incomplete strategy% (11373)------------------------------
% (11373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11373)Termination reason: Refutation not found, incomplete strategy

% (11373)Memory used [KB]: 1663
% (11373)Time elapsed: 0.002 s
% (11373)------------------------------
% (11373)------------------------------
fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f19])).

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
    inference(flattening,[],[f18])).

% (11358)Refutation not found, incomplete strategy% (11358)------------------------------
% (11358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11358)Termination reason: Refutation not found, incomplete strategy

% (11358)Memory used [KB]: 1663
% (11358)Time elapsed: 0.180 s
% (11358)------------------------------
% (11358)------------------------------
fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f88,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f334,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f102,f83,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

% (11348)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f83,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_1
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f102,plain,
    ( ~ r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f325,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl5_2
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f87,f102,f287])).

fof(f287,plain,(
    ! [X10,X11] :
      ( r1_xboole_0(X11,k2_enumset1(X10,X10,X10,X10))
      | r2_hidden(X10,X11) ) ),
    inference(resolution,[],[f279,f119])).

% (11365)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f119,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(X14,X15)
      | r1_xboole_0(X15,X14) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(X14,X15)
      | r1_xboole_0(X15,X14)
      | r1_xboole_0(X15,X14) ) ),
    inference(resolution,[],[f94,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    ! [X14,X12,X13] :
      ( ~ r2_hidden(sK4(X13,X14),X12)
      | ~ r1_xboole_0(X12,X13)
      | r1_xboole_0(X13,X14) ) ),
    inference(resolution,[],[f46,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f279,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(k2_enumset1(X2,X2,X2,X2),X3)
      | r2_hidden(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,X3)
      | r1_xboole_0(k2_enumset1(X2,X2,X2,X2),X3)
      | r1_xboole_0(k2_enumset1(X2,X2,X2,X2),X3) ) ),
    inference(superposition,[],[f45,f107])).

fof(f107,plain,(
    ! [X4,X3] :
      ( sK4(k2_enumset1(X3,X3,X3,X3),X4) = X3
      | r1_xboole_0(k2_enumset1(X3,X3,X3,X3),X4) ) ),
    inference(resolution,[],[f80,f44])).

fof(f80,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f40,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f51])).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f87,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f103,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f98,f82,f100])).

fof(f98,plain,
    ( ~ r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_1 ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,
    ( sK0 != sK0
    | ~ r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_1 ),
    inference(superposition,[],[f84,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f90,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f56,f86,f82])).

fof(f56,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f30,f49,f54])).

fof(f30,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f89,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f55,f86,f82])).

fof(f55,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f31,f49,f54])).

fof(f31,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:32:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.57  % (11367)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.57  % (11359)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.61/0.57  % (11350)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.61/0.58  % (11351)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.61/0.58  % (11349)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.79/0.59  % (11346)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.79/0.60  % (11345)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.79/0.60  % (11345)Refutation not found, incomplete strategy% (11345)------------------------------
% 1.79/0.60  % (11345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (11345)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.60  
% 1.79/0.60  % (11345)Memory used [KB]: 1663
% 1.79/0.60  % (11345)Time elapsed: 0.160 s
% 1.79/0.60  % (11345)------------------------------
% 1.79/0.60  % (11345)------------------------------
% 1.79/0.60  % (11353)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.79/0.60  % (11347)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.79/0.60  % (11369)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.79/0.60  % (11352)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.79/0.60  % (11361)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.79/0.60  % (11361)Refutation not found, incomplete strategy% (11361)------------------------------
% 1.79/0.60  % (11361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.61  % (11366)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.79/0.61  % (11361)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.61  
% 1.79/0.61  % (11361)Memory used [KB]: 1663
% 1.79/0.61  % (11361)Time elapsed: 0.166 s
% 1.79/0.61  % (11361)------------------------------
% 1.79/0.61  % (11361)------------------------------
% 1.79/0.61  % (11367)Refutation found. Thanks to Tanya!
% 1.79/0.61  % SZS status Theorem for theBenchmark
% 1.79/0.61  % (11358)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.79/0.61  % (11373)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.79/0.61  % SZS output start Proof for theBenchmark
% 1.79/0.61  fof(f361,plain,(
% 1.79/0.61    $false),
% 1.79/0.61    inference(avatar_sat_refutation,[],[f89,f90,f103,f325,f334,f360])).
% 1.79/0.61  fof(f360,plain,(
% 1.79/0.61    ~spl5_2 | ~spl5_3),
% 1.79/0.61    inference(avatar_contradiction_clause,[],[f349])).
% 1.79/0.61  fof(f349,plain,(
% 1.79/0.61    $false | (~spl5_2 | ~spl5_3)),
% 1.79/0.61    inference(unit_resulting_resolution,[],[f88,f76,f101,f46])).
% 1.79/0.61  fof(f46,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f28])).
% 1.79/0.61  fof(f28,plain,(
% 1.79/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.79/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f27])).
% 1.79/0.61  fof(f27,plain,(
% 1.79/0.61    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f14,plain,(
% 1.79/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.79/0.61    inference(ennf_transformation,[],[f11])).
% 1.79/0.61  fof(f11,plain,(
% 1.79/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.79/0.61    inference(rectify,[],[f1])).
% 1.79/0.61  fof(f1,axiom,(
% 1.79/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.79/0.61  fof(f101,plain,(
% 1.79/0.61    r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_3),
% 1.79/0.61    inference(avatar_component_clause,[],[f100])).
% 1.79/0.61  fof(f100,plain,(
% 1.79/0.61    spl5_3 <=> r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.79/0.61  fof(f76,plain,(
% 1.79/0.61    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 1.79/0.61    inference(equality_resolution,[],[f75])).
% 1.79/0.61  fof(f75,plain,(
% 1.79/0.61    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 1.79/0.61    inference(equality_resolution,[],[f63])).
% 1.79/0.61  fof(f63,plain,(
% 1.79/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.79/0.61    inference(definition_unfolding,[],[f33,f51])).
% 1.79/0.61  % (11373)Refutation not found, incomplete strategy% (11373)------------------------------
% 1.79/0.61  % (11373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.61  % (11373)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.61  
% 1.79/0.61  % (11373)Memory used [KB]: 1663
% 1.79/0.61  % (11373)Time elapsed: 0.002 s
% 1.79/0.61  % (11373)------------------------------
% 1.79/0.61  % (11373)------------------------------
% 1.79/0.61  fof(f51,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f8])).
% 1.79/0.61  fof(f8,axiom,(
% 1.79/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.79/0.61  fof(f33,plain,(
% 1.79/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.79/0.61    inference(cnf_transformation,[],[f22])).
% 1.79/0.61  fof(f22,plain,(
% 1.79/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.79/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 1.79/0.61  fof(f21,plain,(
% 1.79/0.61    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f20,plain,(
% 1.79/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.79/0.61    inference(rectify,[],[f19])).
% 1.79/0.61  fof(f19,plain,(
% 1.79/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.79/0.61    inference(flattening,[],[f18])).
% 1.79/0.61  % (11358)Refutation not found, incomplete strategy% (11358)------------------------------
% 1.79/0.61  % (11358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.61  % (11358)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.61  
% 1.79/0.61  % (11358)Memory used [KB]: 1663
% 1.79/0.61  % (11358)Time elapsed: 0.180 s
% 1.79/0.61  % (11358)------------------------------
% 1.79/0.61  % (11358)------------------------------
% 1.79/0.61  fof(f18,plain,(
% 1.79/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.79/0.61    inference(nnf_transformation,[],[f13])).
% 1.79/0.61  fof(f13,plain,(
% 1.79/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.79/0.61    inference(ennf_transformation,[],[f4])).
% 1.79/0.61  fof(f4,axiom,(
% 1.79/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.79/0.61  fof(f88,plain,(
% 1.79/0.61    r2_hidden(sK1,sK0) | ~spl5_2),
% 1.79/0.61    inference(avatar_component_clause,[],[f86])).
% 1.79/0.61  fof(f86,plain,(
% 1.79/0.61    spl5_2 <=> r2_hidden(sK1,sK0)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.79/0.61  fof(f334,plain,(
% 1.79/0.61    ~spl5_1 | spl5_3),
% 1.79/0.61    inference(avatar_contradiction_clause,[],[f329])).
% 1.79/0.61  fof(f329,plain,(
% 1.79/0.61    $false | (~spl5_1 | spl5_3)),
% 1.79/0.61    inference(unit_resulting_resolution,[],[f102,f83,f69])).
% 1.79/0.61  fof(f69,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 1.79/0.61    inference(definition_unfolding,[],[f48,f49])).
% 1.79/0.61  fof(f49,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.79/0.61    inference(cnf_transformation,[],[f2])).
% 1.79/0.62  % (11348)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.79/0.62  fof(f2,axiom,(
% 1.79/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.79/0.62  fof(f48,plain,(
% 1.79/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.79/0.62    inference(cnf_transformation,[],[f29])).
% 1.79/0.62  fof(f29,plain,(
% 1.79/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.79/0.62    inference(nnf_transformation,[],[f3])).
% 1.79/0.62  fof(f3,axiom,(
% 1.79/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.79/0.62  fof(f83,plain,(
% 1.79/0.62    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl5_1),
% 1.79/0.62    inference(avatar_component_clause,[],[f82])).
% 1.79/0.62  fof(f82,plain,(
% 1.79/0.62    spl5_1 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.79/0.62  fof(f102,plain,(
% 1.79/0.62    ~r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_3),
% 1.79/0.62    inference(avatar_component_clause,[],[f100])).
% 1.79/0.62  fof(f325,plain,(
% 1.79/0.62    spl5_2 | spl5_3),
% 1.79/0.62    inference(avatar_contradiction_clause,[],[f302])).
% 1.79/0.62  fof(f302,plain,(
% 1.79/0.62    $false | (spl5_2 | spl5_3)),
% 1.79/0.62    inference(unit_resulting_resolution,[],[f87,f102,f287])).
% 1.79/0.62  fof(f287,plain,(
% 1.79/0.62    ( ! [X10,X11] : (r1_xboole_0(X11,k2_enumset1(X10,X10,X10,X10)) | r2_hidden(X10,X11)) )),
% 1.79/0.62    inference(resolution,[],[f279,f119])).
% 1.79/0.62  % (11365)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.79/0.62  fof(f119,plain,(
% 1.79/0.62    ( ! [X14,X15] : (~r1_xboole_0(X14,X15) | r1_xboole_0(X15,X14)) )),
% 1.79/0.62    inference(duplicate_literal_removal,[],[f118])).
% 1.79/0.62  fof(f118,plain,(
% 1.79/0.62    ( ! [X14,X15] : (~r1_xboole_0(X14,X15) | r1_xboole_0(X15,X14) | r1_xboole_0(X15,X14)) )),
% 1.79/0.62    inference(resolution,[],[f94,f45])).
% 1.79/0.62  fof(f45,plain,(
% 1.79/0.62    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f28])).
% 1.79/0.62  fof(f94,plain,(
% 1.79/0.62    ( ! [X14,X12,X13] : (~r2_hidden(sK4(X13,X14),X12) | ~r1_xboole_0(X12,X13) | r1_xboole_0(X13,X14)) )),
% 1.79/0.62    inference(resolution,[],[f46,f44])).
% 1.79/0.62  fof(f44,plain,(
% 1.79/0.62    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f28])).
% 1.79/0.62  fof(f279,plain,(
% 1.79/0.62    ( ! [X2,X3] : (r1_xboole_0(k2_enumset1(X2,X2,X2,X2),X3) | r2_hidden(X2,X3)) )),
% 1.79/0.62    inference(duplicate_literal_removal,[],[f266])).
% 1.79/0.62  fof(f266,plain,(
% 1.79/0.62    ( ! [X2,X3] : (r2_hidden(X2,X3) | r1_xboole_0(k2_enumset1(X2,X2,X2,X2),X3) | r1_xboole_0(k2_enumset1(X2,X2,X2,X2),X3)) )),
% 1.79/0.62    inference(superposition,[],[f45,f107])).
% 1.79/0.62  fof(f107,plain,(
% 1.79/0.62    ( ! [X4,X3] : (sK4(k2_enumset1(X3,X3,X3,X3),X4) = X3 | r1_xboole_0(k2_enumset1(X3,X3,X3,X3),X4)) )),
% 1.79/0.62    inference(resolution,[],[f80,f44])).
% 1.79/0.62  fof(f80,plain,(
% 1.79/0.62    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.79/0.62    inference(equality_resolution,[],[f68])).
% 1.79/0.62  fof(f68,plain,(
% 1.79/0.62    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.79/0.62    inference(definition_unfolding,[],[f40,f54])).
% 1.79/0.62  fof(f54,plain,(
% 1.79/0.62    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.79/0.62    inference(definition_unfolding,[],[f50,f53])).
% 1.79/0.62  fof(f53,plain,(
% 1.79/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.79/0.62    inference(definition_unfolding,[],[f52,f51])).
% 1.79/0.62  fof(f52,plain,(
% 1.79/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f7])).
% 1.79/0.62  fof(f7,axiom,(
% 1.79/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.79/0.62  fof(f50,plain,(
% 1.79/0.62    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f6])).
% 1.79/0.62  fof(f6,axiom,(
% 1.79/0.62    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.79/0.62  fof(f40,plain,(
% 1.79/0.62    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.79/0.62    inference(cnf_transformation,[],[f26])).
% 1.79/0.62  fof(f26,plain,(
% 1.79/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.79/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 1.79/0.62  fof(f25,plain,(
% 1.79/0.62    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.79/0.62    introduced(choice_axiom,[])).
% 1.79/0.62  fof(f24,plain,(
% 1.79/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.79/0.62    inference(rectify,[],[f23])).
% 1.79/0.62  fof(f23,plain,(
% 1.79/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.79/0.62    inference(nnf_transformation,[],[f5])).
% 1.79/0.62  fof(f5,axiom,(
% 1.79/0.62    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.79/0.62  fof(f87,plain,(
% 1.79/0.62    ~r2_hidden(sK1,sK0) | spl5_2),
% 1.79/0.62    inference(avatar_component_clause,[],[f86])).
% 1.79/0.62  fof(f103,plain,(
% 1.79/0.62    ~spl5_3 | spl5_1),
% 1.79/0.62    inference(avatar_split_clause,[],[f98,f82,f100])).
% 1.79/0.62  fof(f98,plain,(
% 1.79/0.62    ~r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_1),
% 1.79/0.62    inference(trivial_inequality_removal,[],[f96])).
% 1.79/0.62  fof(f96,plain,(
% 1.79/0.62    sK0 != sK0 | ~r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_1),
% 1.79/0.62    inference(superposition,[],[f84,f70])).
% 1.79/0.62  fof(f70,plain,(
% 1.79/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.79/0.62    inference(definition_unfolding,[],[f47,f49])).
% 1.79/0.62  fof(f47,plain,(
% 1.79/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f29])).
% 1.79/0.62  fof(f84,plain,(
% 1.79/0.62    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | spl5_1),
% 1.79/0.62    inference(avatar_component_clause,[],[f82])).
% 1.79/0.62  fof(f90,plain,(
% 1.79/0.62    spl5_1 | ~spl5_2),
% 1.79/0.62    inference(avatar_split_clause,[],[f56,f86,f82])).
% 1.79/0.62  fof(f56,plain,(
% 1.79/0.62    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.79/0.62    inference(definition_unfolding,[],[f30,f49,f54])).
% 1.79/0.62  fof(f30,plain,(
% 1.79/0.62    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.79/0.62    inference(cnf_transformation,[],[f17])).
% 1.79/0.62  fof(f17,plain,(
% 1.79/0.62    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.79/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 1.79/0.62  fof(f16,plain,(
% 1.79/0.62    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 1.79/0.62    introduced(choice_axiom,[])).
% 1.79/0.62  fof(f15,plain,(
% 1.79/0.62    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.79/0.62    inference(nnf_transformation,[],[f12])).
% 1.79/0.62  fof(f12,plain,(
% 1.79/0.62    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f10])).
% 1.79/0.62  fof(f10,negated_conjecture,(
% 1.79/0.62    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.79/0.62    inference(negated_conjecture,[],[f9])).
% 1.79/0.62  fof(f9,conjecture,(
% 1.79/0.62    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.79/0.62  fof(f89,plain,(
% 1.79/0.62    ~spl5_1 | spl5_2),
% 1.79/0.62    inference(avatar_split_clause,[],[f55,f86,f82])).
% 1.79/0.62  fof(f55,plain,(
% 1.79/0.62    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.79/0.62    inference(definition_unfolding,[],[f31,f49,f54])).
% 1.79/0.62  fof(f31,plain,(
% 1.79/0.62    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.79/0.62    inference(cnf_transformation,[],[f17])).
% 1.79/0.62  % SZS output end Proof for theBenchmark
% 1.79/0.62  % (11367)------------------------------
% 1.79/0.62  % (11367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.62  % (11367)Termination reason: Refutation
% 1.79/0.62  
% 1.79/0.62  % (11367)Memory used [KB]: 11001
% 1.79/0.62  % (11367)Time elapsed: 0.116 s
% 1.79/0.62  % (11367)------------------------------
% 1.79/0.62  % (11367)------------------------------
% 1.79/0.62  % (11344)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.79/0.62  % (11357)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.79/0.62  % (11343)Success in time 0.254 s
%------------------------------------------------------------------------------
