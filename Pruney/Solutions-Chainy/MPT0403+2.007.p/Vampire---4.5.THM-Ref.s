%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  74 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  200 ( 267 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f61,f69,f109])).

fof(f109,plain,
    ( spl9_2
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f99,f93])).

fof(f93,plain,
    ( ! [X0] : ~ sP1(k2_xboole_0(sK4(k2_setfam_1(sK3,sK3),sK3),X0),sK3,sK3)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f81,f49,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(sK6(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP1(sK6(X0,X1,X2),X1,X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X4,X1,X0) )
            & ( sP1(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(sK6(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP1(sK6(X0,X1,X2),X1,X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X4,X1,X0) )
            & ( sP1(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X3,X1,X0) )
            & ( sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f49,plain,(
    ! [X0,X1] : sP2(X0,X1,k2_setfam_1(X0,X1)) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_setfam_1(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k2_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_setfam_1(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f11,f10])).

fof(f10,plain,(
    ! [X3,X1,X0] :
      ( sP1(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k2_xboole_0(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k2_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_setfam_1)).

fof(f81,plain,
    ( ! [X0] : ~ r2_hidden(k2_xboole_0(sK4(k2_setfam_1(sK3,sK3),sK3),X0),k2_setfam_1(sK3,sK3))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f60,f31,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK4(X0,X1),X3)
      | sP0(X0,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK4(X0,X1),X3)
              | ~ r2_hidden(X3,X0) )
          & r2_hidden(sK4(X0,X1),X1) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK5(X0,X4))
              & r2_hidden(sK5(X0,X4),X0) )
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f18,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK4(X0,X1),X3)
            | ~ r2_hidden(X3,X0) )
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X0) )
     => ( r1_tarski(X4,sK5(X0,X4))
        & r2_hidden(sK5(X0,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X0) )
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f60,plain,
    ( ~ sP0(k2_setfam_1(sK3,sK3),sK3)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl9_2
  <=> sP0(k2_setfam_1(sK3,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f99,plain,
    ( sP1(k2_xboole_0(sK4(k2_setfam_1(sK3,sK3),sK3),sK4(k2_setfam_1(sK3,sK3),sK3)),sK3,sK3)
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f68,f68,f48])).

fof(f48,plain,(
    ! [X4,X2,X3,X1] :
      ( sP1(k2_xboole_0(X3,X4),X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2)
      | k2_xboole_0(X3,X4) != X0
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3,X4] :
            ( k2_xboole_0(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ( k2_xboole_0(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0
          & r2_hidden(sK8(X0,X1,X2),X1)
          & r2_hidden(sK7(X0,X1,X2),X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k2_xboole_0(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k2_xboole_0(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3,X4] :
            ( k2_xboole_0(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ? [X5,X6] :
            ( k2_xboole_0(X5,X6) = X0
            & r2_hidden(X6,X1)
            & r2_hidden(X5,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X3,X1,X0] :
      ( ( sP1(X3,X1,X0)
        | ! [X4,X5] :
            ( k2_xboole_0(X4,X5) != X3
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X0) ) )
      & ( ? [X4,X5] :
            ( k2_xboole_0(X4,X5) = X3
            & r2_hidden(X5,X1)
            & r2_hidden(X4,X0) )
        | ~ sP1(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f68,plain,
    ( r2_hidden(sK4(k2_setfam_1(sK3,sK3),sK3),sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl9_3
  <=> r2_hidden(sK4(k2_setfam_1(sK3,sK3),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f69,plain,
    ( spl9_3
    | spl9_2 ),
    inference(avatar_split_clause,[],[f64,f58,f66])).

fof(f64,plain,
    ( r2_hidden(sK4(k2_setfam_1(sK3,sK3),sK3),sK3)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f60,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,
    ( ~ spl9_2
    | spl9_1 ),
    inference(avatar_split_clause,[],[f55,f51,f58])).

fof(f51,plain,
    ( spl9_1
  <=> r1_setfam_1(sK3,k2_setfam_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f55,plain,
    ( ~ sP0(k2_setfam_1(sK3,sK3),sK3)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f53,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ~ sP0(X1,X0) )
      & ( sP0(X1,X0)
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> sP0(X1,X0) ) ),
    inference(definition_folding,[],[f7,f8])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f53,plain,
    ( ~ r1_setfam_1(sK3,k2_setfam_1(sK3,sK3))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f54,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f30,f51])).

fof(f30,plain,(
    ~ r1_setfam_1(sK3,k2_setfam_1(sK3,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_setfam_1(sK3,k2_setfam_1(sK3,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f6,f13])).

fof(f13,plain,
    ( ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0))
   => ~ r1_setfam_1(sK3,k2_setfam_1(sK3,sK3)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n012.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:58:22 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.41  % (7034)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.41  % (7034)Refutation not found, incomplete strategy% (7034)------------------------------
% 0.21/0.41  % (7034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (7034)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.41  
% 0.21/0.41  % (7034)Memory used [KB]: 1535
% 0.21/0.41  % (7034)Time elapsed: 0.003 s
% 0.21/0.41  % (7034)------------------------------
% 0.21/0.41  % (7034)------------------------------
% 0.21/0.47  % (7037)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (7037)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f54,f61,f69,f109])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    spl9_2 | ~spl9_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    $false | (spl9_2 | ~spl9_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f99,f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X0] : (~sP1(k2_xboole_0(sK4(k2_setfam_1(sK3,sK3),sK3),X0),sK3,sK3)) ) | spl9_2),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f81,f49,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(sK6(X0,X1,X2),X1,X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP1(sK6(X0,X1,X2),X1,X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X4,X1,X0)) & (sP1(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP1(sK6(X0,X1,X2),X1,X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP1(sK6(X0,X1,X2),X1,X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X4,X1,X0)) & (sP1(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.47    inference(rectify,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X3,X1,X0)) & (sP1(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.47    inference(nnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X3,X1,X0)))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (sP2(X0,X1,k2_setfam_1(X0,X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k2_setfam_1(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_setfam_1(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k2_setfam_1(X0,X1) != X2))),
% 0.21/0.47    inference(nnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_setfam_1(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 0.21/0.47    inference(definition_folding,[],[f3,f11,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X3,X1,X0] : (sP1(X3,X1,X0) <=> ? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_setfam_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_setfam_1)).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(k2_xboole_0(sK4(k2_setfam_1(sK3,sK3),sK3),X0),k2_setfam_1(sK3,sK3))) ) | spl9_2),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f60,f31,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~r1_tarski(sK4(X0,X1),X3) | sP0(X0,X1) | ~r2_hidden(X3,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (~r1_tarski(sK4(X0,X1),X3) | ~r2_hidden(X3,X0)) & r2_hidden(sK4(X0,X1),X1))) & (! [X4] : ((r1_tarski(X4,sK5(X0,X4)) & r2_hidden(sK5(X0,X4),X0)) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f18,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1)) => (! [X3] : (~r1_tarski(sK4(X0,X1),X3) | ~r2_hidden(X3,X0)) & r2_hidden(sK4(X0,X1),X1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X4,X0] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X0)) => (r1_tarski(X4,sK5(X0,X4)) & r2_hidden(sK5(X0,X4),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X0)) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~sP0(X1,X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ~sP0(k2_setfam_1(sK3,sK3),sK3) | spl9_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl9_2 <=> sP0(k2_setfam_1(sK3,sK3),sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    sP1(k2_xboole_0(sK4(k2_setfam_1(sK3,sK3),sK3),sK4(k2_setfam_1(sK3,sK3),sK3)),sK3,sK3) | ~spl9_3),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f68,f68,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X4,X2,X3,X1] : (sP1(k2_xboole_0(X3,X4),X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 0.21/0.47    inference(equality_resolution,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2) | k2_xboole_0(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3,X4] : (k2_xboole_0(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k2_xboole_0(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0 & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2)) | ~sP1(X0,X1,X2)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f26,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X5,X6] : (k2_xboole_0(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k2_xboole_0(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0 & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3,X4] : (k2_xboole_0(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k2_xboole_0(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP1(X0,X1,X2)))),
% 0.21/0.47    inference(rectify,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X3,X1,X0] : ((sP1(X3,X1,X0) | ! [X4,X5] : (k2_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP1(X3,X1,X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f10])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    r2_hidden(sK4(k2_setfam_1(sK3,sK3),sK3),sK3) | ~spl9_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl9_3 <=> r2_hidden(sK4(k2_setfam_1(sK3,sK3),sK3),sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl9_3 | spl9_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f64,f58,f66])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    r2_hidden(sK4(k2_setfam_1(sK3,sK3),sK3),sK3) | spl9_2),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f60,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | sP0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ~spl9_2 | spl9_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f55,f51,f58])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl9_1 <=> r1_setfam_1(sK3,k2_setfam_1(sK3,sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ~sP0(k2_setfam_1(sK3,sK3),sK3) | spl9_1),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f53,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~sP0(X1,X0) | r1_setfam_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> sP0(X1,X0))),
% 0.21/0.47    inference(definition_folding,[],[f7,f8])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ~r1_setfam_1(sK3,k2_setfam_1(sK3,sK3)) | spl9_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f51])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~spl9_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f51])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ~r1_setfam_1(sK3,k2_setfam_1(sK3,sK3))),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ~r1_setfam_1(sK3,k2_setfam_1(sK3,sK3))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f6,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : ~r1_setfam_1(X0,k2_setfam_1(X0,X0)) => ~r1_setfam_1(sK3,k2_setfam_1(sK3,sK3))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0] : ~r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_setfam_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (7037)------------------------------
% 0.21/0.47  % (7037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7037)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (7037)Memory used [KB]: 10618
% 0.21/0.47  % (7037)Time elapsed: 0.064 s
% 0.21/0.47  % (7037)------------------------------
% 0.21/0.47  % (7037)------------------------------
% 0.21/0.48  % (7020)Success in time 0.119 s
%------------------------------------------------------------------------------
