%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:04 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 200 expanded)
%              Number of leaves         :   16 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  191 ( 368 expanded)
%              Number of equality atoms :  118 ( 272 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f146,f232,f237])).

fof(f237,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f131,f231,f129])).

% (13304)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (13294)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (13292)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f129,plain,(
    ! [X2,X0,X5,X3] :
      ( ~ sP0(X0,X5,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

% (13311)Refutation not found, incomplete strategy% (13311)------------------------------
% (13311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK6(X0,X1,X2,X3) != X0
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X0
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X2
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
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
     => ( ( ( sK6(X0,X1,X2,X3) != X0
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X0
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X2
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
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
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f231,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl8_4
  <=> r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f131,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f81,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f70,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f72,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f83,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f84,f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f28,f30])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f232,plain,
    ( ~ spl8_4
    | spl8_1 ),
    inference(avatar_split_clause,[],[f227,f143,f229])).

fof(f143,plain,
    ( spl8_1
  <=> k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f227,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_1 ),
    inference(resolution,[],[f226,f131])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ sP0(sK4,sK3,sK3,X0)
        | ~ r2_hidden(sK3,X0) )
    | spl8_1 ),
    inference(trivial_inequality_removal,[],[f221])).

fof(f221,plain,
    ( ! [X0] :
        ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
        | ~ sP0(sK4,sK3,sK3,X0)
        | ~ r2_hidden(sK3,X0) )
    | spl8_1 ),
    inference(superposition,[],[f196,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f111,f111])).

fof(f111,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f110])).

fof(f110,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f109])).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f196,plain,
    ( ! [X0] :
        ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
        | ~ sP0(sK4,sK3,sK3,X0) )
    | spl8_1 ),
    inference(superposition,[],[f150,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f150,plain,
    ( ! [X0] :
        ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)
        | ~ sP0(sK4,sK3,sK3,X0) )
    | spl8_1 ),
    inference(superposition,[],[f145,f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | ~ sP0(X2,X1,X0,X3) ) ),
    inference(definition_unfolding,[],[f82,f109])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP0(X2,X1,X0,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f145,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f146,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f114,f143])).

fof(f114,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f55,f111,f111,f110])).

fof(f55,plain,(
    k1_tarski(sK3) != k3_xboole_0(k1_tarski(sK3),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    k1_tarski(sK3) != k3_xboole_0(k1_tarski(sK3),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f35])).

fof(f35,plain,
    ( ? [X0,X1] : k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k1_tarski(sK3) != k3_xboole_0(k1_tarski(sK3),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] : k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (13290)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (13286)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (13286)Refutation not found, incomplete strategy% (13286)------------------------------
% 0.20/0.50  % (13286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13286)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13286)Memory used [KB]: 1663
% 0.20/0.50  % (13286)Time elapsed: 0.081 s
% 0.20/0.50  % (13286)------------------------------
% 0.20/0.50  % (13286)------------------------------
% 0.20/0.51  % (13291)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (13311)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.51  % (13303)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.19/0.51  % (13288)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.19/0.51  % (13298)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.19/0.52  % (13308)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.19/0.52  % (13303)Refutation not found, incomplete strategy% (13303)------------------------------
% 1.19/0.52  % (13303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (13285)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.19/0.52  % (13312)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.19/0.52  % (13289)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.19/0.52  % (13302)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.19/0.52  % (13309)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.19/0.52  % (13287)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.19/0.52  % (13293)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.19/0.52  % (13302)Refutation not found, incomplete strategy% (13302)------------------------------
% 1.19/0.52  % (13302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (13300)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.19/0.53  % (13296)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.32/0.53  % (13303)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (13303)Memory used [KB]: 1791
% 1.32/0.53  % (13303)Time elapsed: 0.119 s
% 1.32/0.53  % (13303)------------------------------
% 1.32/0.53  % (13303)------------------------------
% 1.32/0.53  % (13297)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.32/0.53  % (13297)Refutation not found, incomplete strategy% (13297)------------------------------
% 1.32/0.53  % (13297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (13297)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (13297)Memory used [KB]: 10618
% 1.32/0.53  % (13297)Time elapsed: 0.129 s
% 1.32/0.53  % (13297)------------------------------
% 1.32/0.53  % (13297)------------------------------
% 1.32/0.53  % (13301)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.32/0.53  % (13301)Refutation not found, incomplete strategy% (13301)------------------------------
% 1.32/0.53  % (13301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (13301)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (13301)Memory used [KB]: 10746
% 1.32/0.53  % (13301)Time elapsed: 0.122 s
% 1.32/0.53  % (13301)------------------------------
% 1.32/0.53  % (13301)------------------------------
% 1.32/0.53  % (13312)Refutation not found, incomplete strategy% (13312)------------------------------
% 1.32/0.53  % (13312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (13312)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (13312)Memory used [KB]: 6268
% 1.32/0.53  % (13312)Time elapsed: 0.131 s
% 1.32/0.53  % (13312)------------------------------
% 1.32/0.53  % (13312)------------------------------
% 1.32/0.54  % (13295)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.32/0.54  % (13315)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.32/0.54  % (13315)Refutation not found, incomplete strategy% (13315)------------------------------
% 1.32/0.54  % (13315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (13315)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (13315)Memory used [KB]: 1663
% 1.32/0.54  % (13315)Time elapsed: 0.129 s
% 1.32/0.54  % (13315)------------------------------
% 1.32/0.54  % (13315)------------------------------
% 1.32/0.54  % (13299)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.32/0.54  % (13299)Refutation not found, incomplete strategy% (13299)------------------------------
% 1.32/0.54  % (13299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (13299)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (13299)Memory used [KB]: 1791
% 1.32/0.54  % (13299)Time elapsed: 0.140 s
% 1.32/0.54  % (13299)------------------------------
% 1.32/0.54  % (13299)------------------------------
% 1.32/0.54  % (13314)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.54  % (13307)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.32/0.55  % (13310)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.55  % (13306)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.32/0.55  % (13302)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (13302)Memory used [KB]: 1791
% 1.32/0.55  % (13302)Time elapsed: 0.125 s
% 1.32/0.55  % (13302)------------------------------
% 1.32/0.55  % (13302)------------------------------
% 1.32/0.55  % (13310)Refutation not found, incomplete strategy% (13310)------------------------------
% 1.32/0.55  % (13310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (13310)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (13310)Memory used [KB]: 10746
% 1.32/0.55  % (13310)Time elapsed: 0.121 s
% 1.32/0.55  % (13310)------------------------------
% 1.32/0.55  % (13310)------------------------------
% 1.32/0.55  % (13295)Refutation found. Thanks to Tanya!
% 1.32/0.55  % SZS status Theorem for theBenchmark
% 1.32/0.55  % SZS output start Proof for theBenchmark
% 1.32/0.55  fof(f238,plain,(
% 1.32/0.55    $false),
% 1.32/0.55    inference(avatar_sat_refutation,[],[f146,f232,f237])).
% 1.32/0.55  fof(f237,plain,(
% 1.32/0.55    spl8_4),
% 1.32/0.55    inference(avatar_contradiction_clause,[],[f234])).
% 1.32/0.55  fof(f234,plain,(
% 1.32/0.55    $false | spl8_4),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f131,f231,f129])).
% 1.32/0.55  % (13304)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.32/0.55  % (13294)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.32/0.55  % (13292)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.32/0.56  fof(f129,plain,(
% 1.32/0.56    ( ! [X2,X0,X5,X3] : (~sP0(X0,X5,X2,X3) | r2_hidden(X5,X3)) )),
% 1.32/0.56    inference(equality_resolution,[],[f75])).
% 1.32/0.56  fof(f75,plain,(
% 1.32/0.56    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f45])).
% 1.32/0.56  % (13311)Refutation not found, incomplete strategy% (13311)------------------------------
% 1.32/0.56  % (13311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  fof(f45,plain,(
% 1.32/0.56    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.32/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 1.32/0.56  fof(f44,plain,(
% 1.32/0.56    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 1.32/0.56    introduced(choice_axiom,[])).
% 1.32/0.56  fof(f43,plain,(
% 1.32/0.56    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.32/0.56    inference(rectify,[],[f42])).
% 1.32/0.56  fof(f42,plain,(
% 1.32/0.56    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.32/0.56    inference(flattening,[],[f41])).
% 1.32/0.56  fof(f41,plain,(
% 1.32/0.56    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.32/0.56    inference(nnf_transformation,[],[f30])).
% 1.32/0.56  fof(f30,plain,(
% 1.32/0.56    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.32/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.32/0.56  fof(f231,plain,(
% 1.32/0.56    ~r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_4),
% 1.32/0.56    inference(avatar_component_clause,[],[f229])).
% 1.32/0.56  fof(f229,plain,(
% 1.32/0.56    spl8_4 <=> r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.32/0.56  fof(f131,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 1.32/0.56    inference(equality_resolution,[],[f121])).
% 1.32/0.56  fof(f121,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.32/0.56    inference(definition_unfolding,[],[f81,f109])).
% 1.32/0.56  fof(f109,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f70,f108])).
% 1.32/0.56  fof(f108,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f72,f107])).
% 1.32/0.56  fof(f107,plain,(
% 1.32/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f83,f106])).
% 1.32/0.56  fof(f106,plain,(
% 1.32/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f84,f85])).
% 1.32/0.56  fof(f85,plain,(
% 1.32/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f21])).
% 1.32/0.56  fof(f21,axiom,(
% 1.32/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.32/0.56  fof(f84,plain,(
% 1.32/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f20])).
% 1.32/0.56  fof(f20,axiom,(
% 1.32/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.32/0.56  fof(f83,plain,(
% 1.32/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f19])).
% 1.32/0.56  fof(f19,axiom,(
% 1.32/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.32/0.56  fof(f72,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f18])).
% 1.32/0.56  fof(f18,axiom,(
% 1.32/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.32/0.56  fof(f70,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f17])).
% 1.32/0.56  fof(f17,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.56  fof(f81,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.32/0.56    inference(cnf_transformation,[],[f46])).
% 1.32/0.56  fof(f46,plain,(
% 1.32/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.32/0.56    inference(nnf_transformation,[],[f31])).
% 1.32/0.56  fof(f31,plain,(
% 1.32/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.32/0.56    inference(definition_folding,[],[f28,f30])).
% 1.32/0.56  fof(f28,plain,(
% 1.32/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.32/0.56    inference(ennf_transformation,[],[f9])).
% 1.32/0.56  fof(f9,axiom,(
% 1.32/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.32/0.56  fof(f232,plain,(
% 1.32/0.56    ~spl8_4 | spl8_1),
% 1.32/0.56    inference(avatar_split_clause,[],[f227,f143,f229])).
% 1.32/0.56  fof(f143,plain,(
% 1.32/0.56    spl8_1 <=> k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.32/0.56  fof(f227,plain,(
% 1.32/0.56    ~r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_1),
% 1.32/0.56    inference(resolution,[],[f226,f131])).
% 1.32/0.56  fof(f226,plain,(
% 1.32/0.56    ( ! [X0] : (~sP0(sK4,sK3,sK3,X0) | ~r2_hidden(sK3,X0)) ) | spl8_1),
% 1.32/0.56    inference(trivial_inequality_removal,[],[f221])).
% 1.32/0.56  fof(f221,plain,(
% 1.32/0.56    ( ! [X0] : (k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~sP0(sK4,sK3,sK3,X0) | ~r2_hidden(sK3,X0)) ) | spl8_1),
% 1.32/0.56    inference(superposition,[],[f196,f115])).
% 1.32/0.56  fof(f115,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,X1)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f65,f111,f111])).
% 1.32/0.56  fof(f111,plain,(
% 1.32/0.56    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f58,f110])).
% 1.32/0.56  fof(f110,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f62,f109])).
% 1.32/0.56  fof(f62,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f16])).
% 1.32/0.56  fof(f16,axiom,(
% 1.32/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.56  fof(f58,plain,(
% 1.32/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f15])).
% 1.32/0.56  fof(f15,axiom,(
% 1.32/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.56  fof(f65,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f27])).
% 1.32/0.56  fof(f27,plain,(
% 1.32/0.56    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.32/0.56    inference(ennf_transformation,[],[f22])).
% 1.32/0.56  fof(f22,axiom,(
% 1.32/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.32/0.56  fof(f196,plain,(
% 1.32/0.56    ( ! [X0] : (k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~sP0(sK4,sK3,sK3,X0)) ) | spl8_1),
% 1.32/0.56    inference(superposition,[],[f150,f60])).
% 1.32/0.56  fof(f60,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f1])).
% 1.32/0.56  fof(f1,axiom,(
% 1.32/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.32/0.56  fof(f150,plain,(
% 1.32/0.56    ( ! [X0] : (k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) | ~sP0(sK4,sK3,sK3,X0)) ) | spl8_1),
% 1.32/0.56    inference(superposition,[],[f145,f120])).
% 1.32/0.56  fof(f120,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f82,f109])).
% 1.32/0.56  fof(f82,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f46])).
% 1.32/0.56  fof(f145,plain,(
% 1.32/0.56    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_1),
% 1.32/0.56    inference(avatar_component_clause,[],[f143])).
% 1.32/0.56  fof(f146,plain,(
% 1.32/0.56    ~spl8_1),
% 1.32/0.56    inference(avatar_split_clause,[],[f114,f143])).
% 1.32/0.56  fof(f114,plain,(
% 1.32/0.56    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 1.32/0.56    inference(definition_unfolding,[],[f55,f111,f111,f110])).
% 1.32/0.56  fof(f55,plain,(
% 1.32/0.56    k1_tarski(sK3) != k3_xboole_0(k1_tarski(sK3),k2_tarski(sK3,sK4))),
% 1.32/0.56    inference(cnf_transformation,[],[f36])).
% 1.32/0.56  fof(f36,plain,(
% 1.32/0.56    k1_tarski(sK3) != k3_xboole_0(k1_tarski(sK3),k2_tarski(sK3,sK4))),
% 1.32/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f35])).
% 1.32/0.56  fof(f35,plain,(
% 1.32/0.56    ? [X0,X1] : k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k1_tarski(sK3) != k3_xboole_0(k1_tarski(sK3),k2_tarski(sK3,sK4))),
% 1.32/0.56    introduced(choice_axiom,[])).
% 1.32/0.56  fof(f26,plain,(
% 1.32/0.56    ? [X0,X1] : k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.32/0.56    inference(ennf_transformation,[],[f24])).
% 1.32/0.56  fof(f24,negated_conjecture,(
% 1.32/0.56    ~! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.32/0.56    inference(negated_conjecture,[],[f23])).
% 1.32/0.56  fof(f23,conjecture,(
% 1.32/0.56    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 1.32/0.56  % SZS output end Proof for theBenchmark
% 1.32/0.56  % (13295)------------------------------
% 1.32/0.56  % (13295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (13295)Termination reason: Refutation
% 1.32/0.56  
% 1.32/0.56  % (13295)Memory used [KB]: 10874
% 1.32/0.56  % (13295)Time elapsed: 0.142 s
% 1.32/0.56  % (13295)------------------------------
% 1.32/0.56  % (13295)------------------------------
% 1.32/0.57  % (13281)Success in time 0.204 s
%------------------------------------------------------------------------------
