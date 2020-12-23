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
% DateTime   : Thu Dec  3 12:41:37 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 284 expanded)
%              Number of leaves         :   29 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  348 (1105 expanded)
%              Number of equality atoms :   52 ( 207 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f92,f97,f102,f206,f212,f230,f240,f243,f263,f281,f295,f309,f317,f331,f336,f337])).

fof(f337,plain,
    ( sK0 != k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | r1_tarski(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f336,plain,(
    spl5_22 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | spl5_22 ),
    inference(unit_resulting_resolution,[],[f64,f326])).

fof(f326,plain,
    ( ~ r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl5_22
  <=> r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f37,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f331,plain,
    ( ~ spl5_22
    | spl5_23
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f319,f314,f328,f324])).

fof(f328,plain,
    ( spl5_23
  <=> sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f314,plain,
    ( spl5_21
  <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f319,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl5_21 ),
    inference(resolution,[],[f316,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f316,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f314])).

fof(f317,plain,
    ( spl5_21
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f312,f260,f314])).

fof(f260,plain,
    ( spl5_20
  <=> r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f312,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0)
    | ~ spl5_20 ),
    inference(resolution,[],[f262,f77])).

fof(f77,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f262,plain,
    ( r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f260])).

fof(f309,plain,(
    ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f64,f258,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f258,plain,
    ( ! [X0] : ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl5_19
  <=> ! [X0] : ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f295,plain,(
    ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f64,f235,f76])).

fof(f235,plain,
    ( ! [X1] : ~ r2_hidden(sK1,X1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl5_17
  <=> ! [X1] : ~ r2_hidden(sK1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f281,plain,
    ( spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f280,f227,f89])).

fof(f89,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f227,plain,
    ( spl5_16
  <=> sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f280,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_16 ),
    inference(superposition,[],[f64,f229])).

fof(f229,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f227])).

fof(f263,plain,
    ( spl5_19
    | spl5_20
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f255,f204,f260,f257])).

fof(f204,plain,
    ( spl5_13
  <=> ! [X1] : ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f255,plain,
    ( ! [X0] :
        ( r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0))
        | ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f205,f78])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f205,plain,
    ( ! [X1] : ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f204])).

fof(f243,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f72,f239,f76])).

fof(f239,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK1))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl5_18
  <=> r2_hidden(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f240,plain,
    ( spl5_17
    | ~ spl5_18
    | ~ spl5_4
    | spl5_15 ),
    inference(avatar_split_clause,[],[f232,f223,f99,f237,f234])).

fof(f99,plain,
    ( spl5_4
  <=> k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f223,plain,
    ( spl5_15
  <=> r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f232,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,k1_zfmisc_1(sK1))
        | ~ r2_hidden(sK1,X1) )
    | ~ spl5_4
    | spl5_15 ),
    inference(resolution,[],[f225,f190])).

% (17095)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (17087)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (17087)Refutation not found, incomplete strategy% (17087)------------------------------
% (17087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17087)Termination reason: Refutation not found, incomplete strategy

% (17087)Memory used [KB]: 1791
% (17087)Time elapsed: 0.170 s
% (17087)------------------------------
% (17087)------------------------------
fof(f190,plain,
    ( ! [X4,X3] :
        ( r1_tarski(X3,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
        | ~ r2_hidden(X3,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X3,X4) )
    | ~ spl5_4 ),
    inference(resolution,[],[f143,f77])).

fof(f143,plain,
    ( ! [X6,X7] :
        ( r2_hidden(X6,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
        | ~ r2_hidden(X6,X7)
        | ~ r2_hidden(X6,k1_zfmisc_1(sK1)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f113,f79])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f113,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X5,k4_xboole_0(k4_xboole_0(X4,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1)))
        | r2_hidden(X5,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
        | ~ r2_hidden(X5,X4) )
    | ~ spl5_4 ),
    inference(superposition,[],[f78,f103])).

fof(f103,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(X0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1)) = k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
    | ~ spl5_4 ),
    inference(superposition,[],[f70,f101])).

fof(f101,plain,
    ( k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f70,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f54,f61])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f225,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f223])).

fof(f230,plain,
    ( ~ spl5_15
    | spl5_16
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f213,f209,f227,f223])).

fof(f209,plain,
    ( spl5_14
  <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f213,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl5_14 ),
    inference(resolution,[],[f211,f43])).

fof(f211,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f209])).

fof(f212,plain,
    ( spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f207,f200,f209])).

fof(f200,plain,
    ( spl5_12
  <=> r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f207,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1)
    | ~ spl5_12 ),
    inference(resolution,[],[f202,f77])).

fof(f202,plain,
    ( r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f200])).

fof(f206,plain,
    ( spl5_12
    | spl5_13
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f137,f99,f204,f200])).

fof(f137,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0)))
        | r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f131,f72])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(sK0)))
        | r2_hidden(X0,k1_zfmisc_1(sK1)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f118,f76])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
        | r2_hidden(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(sK0))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f112,f78])).

fof(f112,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k4_xboole_0(k4_xboole_0(X2,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1)))
        | ~ r2_hidden(X3,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f79,f103])).

fof(f102,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f63,f99])).

fof(f63,plain,(
    k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f34,f61,f61])).

fof(f34,plain,(
    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ~ r3_xboole_0(X0,X1)
        & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) )
   => ( ~ r3_xboole_0(sK0,sK1)
      & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
       => r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
     => r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(f97,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f87,f82,f94])).

fof(f94,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f82,plain,
    ( spl5_1
  <=> r3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f87,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl5_1 ),
    inference(resolution,[],[f84,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ( ~ r1_tarski(X1,X0)
        & ~ r1_tarski(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) )
     => r3_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f84,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f92,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f86,f82,f89])).

fof(f86,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_1 ),
    inference(resolution,[],[f84,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f85,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f35,f82])).

fof(f35,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:59:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (17075)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (17073)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.50  % (17069)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (17093)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (17096)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (17096)Refutation not found, incomplete strategy% (17096)------------------------------
% 0.21/0.51  % (17096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17096)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17096)Memory used [KB]: 6268
% 0.21/0.51  % (17096)Time elapsed: 0.115 s
% 0.21/0.51  % (17096)------------------------------
% 0.21/0.51  % (17096)------------------------------
% 0.21/0.51  % (17074)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (17072)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (17098)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (17077)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (17088)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (17085)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (17083)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (17098)Refutation not found, incomplete strategy% (17098)------------------------------
% 0.21/0.52  % (17098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17098)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17098)Memory used [KB]: 1663
% 0.21/0.52  % (17098)Time elapsed: 0.117 s
% 0.21/0.52  % (17098)------------------------------
% 0.21/0.52  % (17098)------------------------------
% 0.21/0.52  % (17083)Refutation not found, incomplete strategy% (17083)------------------------------
% 0.21/0.52  % (17083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17083)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17083)Memory used [KB]: 1663
% 0.21/0.52  % (17083)Time elapsed: 0.115 s
% 0.21/0.52  % (17083)------------------------------
% 0.21/0.52  % (17083)------------------------------
% 0.21/0.52  % (17081)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (17085)Refutation not found, incomplete strategy% (17085)------------------------------
% 0.21/0.52  % (17085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17085)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (17085)Memory used [KB]: 10618
% 0.21/0.53  % (17085)Time elapsed: 0.128 s
% 0.21/0.53  % (17085)------------------------------
% 0.21/0.53  % (17085)------------------------------
% 1.26/0.53  % (17082)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.26/0.53  % (17070)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.26/0.53  % (17070)Refutation not found, incomplete strategy% (17070)------------------------------
% 1.26/0.53  % (17070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (17070)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (17070)Memory used [KB]: 1663
% 1.26/0.53  % (17070)Time elapsed: 0.126 s
% 1.26/0.53  % (17070)------------------------------
% 1.26/0.53  % (17070)------------------------------
% 1.26/0.53  % (17079)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.26/0.53  % (17097)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.26/0.53  % (17094)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.26/0.53  % (17084)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.26/0.53  % (17090)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.26/0.54  % (17086)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.26/0.54  % (17092)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.26/0.54  % (17071)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.51/0.54  % (17089)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.51/0.54  % (17078)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.51/0.55  % (17091)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.51/0.55  % (17080)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.51/0.55  % (17076)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.51/0.56  % (17079)Refutation found. Thanks to Tanya!
% 1.51/0.56  % SZS status Theorem for theBenchmark
% 1.51/0.56  % SZS output start Proof for theBenchmark
% 1.51/0.56  fof(f338,plain,(
% 1.51/0.56    $false),
% 1.51/0.56    inference(avatar_sat_refutation,[],[f85,f92,f97,f102,f206,f212,f230,f240,f243,f263,f281,f295,f309,f317,f331,f336,f337])).
% 1.51/0.56  fof(f337,plain,(
% 1.51/0.56    sK0 != k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | r1_tarski(sK1,sK0)),
% 1.51/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.51/0.56  fof(f336,plain,(
% 1.51/0.56    spl5_22),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f332])).
% 1.51/0.56  fof(f332,plain,(
% 1.51/0.56    $false | spl5_22),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f64,f326])).
% 1.51/0.56  fof(f326,plain,(
% 1.51/0.56    ~r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | spl5_22),
% 1.51/0.56    inference(avatar_component_clause,[],[f324])).
% 1.51/0.56  fof(f324,plain,(
% 1.51/0.56    spl5_22 <=> r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.51/0.56  fof(f64,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 1.51/0.56    inference(definition_unfolding,[],[f37,f61])).
% 1.51/0.56  fof(f61,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.51/0.56    inference(definition_unfolding,[],[f39,f40])).
% 1.51/0.56  fof(f40,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f9])).
% 1.51/0.56  fof(f9,axiom,(
% 1.51/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.51/0.56  fof(f39,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f11])).
% 1.51/0.56  fof(f11,axiom,(
% 1.51/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.51/0.56  fof(f37,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f5])).
% 1.51/0.56  fof(f5,axiom,(
% 1.51/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.51/0.56  fof(f331,plain,(
% 1.51/0.56    ~spl5_22 | spl5_23 | ~spl5_21),
% 1.51/0.56    inference(avatar_split_clause,[],[f319,f314,f328,f324])).
% 1.51/0.56  fof(f328,plain,(
% 1.51/0.56    spl5_23 <=> sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.51/0.56  fof(f314,plain,(
% 1.51/0.56    spl5_21 <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.51/0.56  fof(f319,plain,(
% 1.51/0.56    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~spl5_21),
% 1.51/0.56    inference(resolution,[],[f316,f43])).
% 1.51/0.56  fof(f43,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f20])).
% 1.51/0.56  fof(f20,plain,(
% 1.51/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.56    inference(flattening,[],[f19])).
% 1.51/0.56  fof(f19,plain,(
% 1.51/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.56    inference(nnf_transformation,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.51/0.56  fof(f316,plain,(
% 1.51/0.56    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0) | ~spl5_21),
% 1.51/0.56    inference(avatar_component_clause,[],[f314])).
% 1.51/0.56  fof(f317,plain,(
% 1.51/0.56    spl5_21 | ~spl5_20),
% 1.51/0.56    inference(avatar_split_clause,[],[f312,f260,f314])).
% 1.51/0.56  fof(f260,plain,(
% 1.51/0.56    spl5_20 <=> r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.51/0.56  fof(f312,plain,(
% 1.51/0.56    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0) | ~spl5_20),
% 1.51/0.56    inference(resolution,[],[f262,f77])).
% 1.51/0.56  fof(f77,plain,(
% 1.51/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.51/0.56    inference(equality_resolution,[],[f50])).
% 1.51/0.56  fof(f50,plain,(
% 1.51/0.56    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f28])).
% 1.51/0.56  fof(f28,plain,(
% 1.51/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 1.51/0.56  fof(f27,plain,(
% 1.51/0.56    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f26,plain,(
% 1.51/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.51/0.56    inference(rectify,[],[f25])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.51/0.56    inference(nnf_transformation,[],[f10])).
% 1.51/0.56  fof(f10,axiom,(
% 1.51/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.51/0.56  fof(f262,plain,(
% 1.51/0.56    r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl5_20),
% 1.51/0.56    inference(avatar_component_clause,[],[f260])).
% 1.51/0.56  fof(f309,plain,(
% 1.51/0.56    ~spl5_19),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f301])).
% 1.51/0.56  fof(f301,plain,(
% 1.51/0.56    $false | ~spl5_19),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f64,f258,f76])).
% 1.51/0.56  fof(f76,plain,(
% 1.51/0.56    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.51/0.56    inference(equality_resolution,[],[f51])).
% 1.51/0.56  fof(f51,plain,(
% 1.51/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f28])).
% 1.51/0.56  fof(f258,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0)) ) | ~spl5_19),
% 1.51/0.56    inference(avatar_component_clause,[],[f257])).
% 1.51/0.56  fof(f257,plain,(
% 1.51/0.56    spl5_19 <=> ! [X0] : ~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.51/0.56  fof(f295,plain,(
% 1.51/0.56    ~spl5_17),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f285])).
% 1.51/0.56  fof(f285,plain,(
% 1.51/0.56    $false | ~spl5_17),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f64,f235,f76])).
% 1.51/0.56  fof(f235,plain,(
% 1.51/0.56    ( ! [X1] : (~r2_hidden(sK1,X1)) ) | ~spl5_17),
% 1.51/0.56    inference(avatar_component_clause,[],[f234])).
% 1.51/0.56  fof(f234,plain,(
% 1.51/0.56    spl5_17 <=> ! [X1] : ~r2_hidden(sK1,X1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.51/0.56  fof(f281,plain,(
% 1.51/0.56    spl5_2 | ~spl5_16),
% 1.51/0.56    inference(avatar_split_clause,[],[f280,f227,f89])).
% 1.51/0.56  fof(f89,plain,(
% 1.51/0.56    spl5_2 <=> r1_tarski(sK0,sK1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.51/0.56  fof(f227,plain,(
% 1.51/0.56    spl5_16 <=> sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.51/0.56  fof(f280,plain,(
% 1.51/0.56    r1_tarski(sK0,sK1) | ~spl5_16),
% 1.51/0.56    inference(superposition,[],[f64,f229])).
% 1.51/0.56  fof(f229,plain,(
% 1.51/0.56    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl5_16),
% 1.51/0.56    inference(avatar_component_clause,[],[f227])).
% 1.51/0.56  fof(f263,plain,(
% 1.51/0.56    spl5_19 | spl5_20 | ~spl5_13),
% 1.51/0.56    inference(avatar_split_clause,[],[f255,f204,f260,f257])).
% 1.51/0.56  fof(f204,plain,(
% 1.51/0.56    spl5_13 <=> ! [X1] : ~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0)))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.51/0.56  fof(f255,plain,(
% 1.51/0.56    ( ! [X0] : (r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0)) | ~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0)) ) | ~spl5_13),
% 1.51/0.56    inference(resolution,[],[f205,f78])).
% 1.51/0.56  fof(f78,plain,(
% 1.51/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.51/0.56    inference(equality_resolution,[],[f57])).
% 1.51/0.56  fof(f57,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.51/0.56    inference(cnf_transformation,[],[f33])).
% 1.51/0.56  fof(f33,plain,(
% 1.51/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 1.51/0.56  fof(f32,plain,(
% 1.51/0.56    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f31,plain,(
% 1.51/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.51/0.56    inference(rectify,[],[f30])).
% 1.51/0.56  fof(f30,plain,(
% 1.51/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.51/0.56    inference(flattening,[],[f29])).
% 1.51/0.56  fof(f29,plain,(
% 1.51/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.51/0.56    inference(nnf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.51/0.56  fof(f205,plain,(
% 1.51/0.56    ( ! [X1] : (~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0)))) ) | ~spl5_13),
% 1.51/0.56    inference(avatar_component_clause,[],[f204])).
% 1.51/0.56  fof(f243,plain,(
% 1.51/0.56    spl5_18),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f241])).
% 1.51/0.56  fof(f241,plain,(
% 1.51/0.56    $false | spl5_18),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f72,f239,f76])).
% 1.51/0.56  fof(f239,plain,(
% 1.51/0.56    ~r2_hidden(sK1,k1_zfmisc_1(sK1)) | spl5_18),
% 1.51/0.56    inference(avatar_component_clause,[],[f237])).
% 1.51/0.56  fof(f237,plain,(
% 1.51/0.56    spl5_18 <=> r2_hidden(sK1,k1_zfmisc_1(sK1))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.51/0.56  fof(f72,plain,(
% 1.51/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.51/0.56    inference(equality_resolution,[],[f41])).
% 1.51/0.56  fof(f41,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f20])).
% 1.51/0.56  fof(f240,plain,(
% 1.51/0.56    spl5_17 | ~spl5_18 | ~spl5_4 | spl5_15),
% 1.51/0.56    inference(avatar_split_clause,[],[f232,f223,f99,f237,f234])).
% 1.51/0.56  fof(f99,plain,(
% 1.51/0.56    spl5_4 <=> k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.51/0.56  fof(f223,plain,(
% 1.51/0.56    spl5_15 <=> r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.51/0.56  fof(f232,plain,(
% 1.51/0.56    ( ! [X1] : (~r2_hidden(sK1,k1_zfmisc_1(sK1)) | ~r2_hidden(sK1,X1)) ) | (~spl5_4 | spl5_15)),
% 1.51/0.56    inference(resolution,[],[f225,f190])).
% 1.51/0.56  % (17095)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.51/0.57  % (17087)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.51/0.57  % (17087)Refutation not found, incomplete strategy% (17087)------------------------------
% 1.51/0.57  % (17087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (17087)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (17087)Memory used [KB]: 1791
% 1.51/0.57  % (17087)Time elapsed: 0.170 s
% 1.51/0.57  % (17087)------------------------------
% 1.51/0.57  % (17087)------------------------------
% 1.51/0.58  fof(f190,plain,(
% 1.51/0.58    ( ! [X4,X3] : (r1_tarski(X3,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~r2_hidden(X3,k1_zfmisc_1(sK1)) | ~r2_hidden(X3,X4)) ) | ~spl5_4),
% 1.51/0.58    inference(resolution,[],[f143,f77])).
% 1.51/0.58  fof(f143,plain,(
% 1.51/0.58    ( ! [X6,X7] : (r2_hidden(X6,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | ~r2_hidden(X6,X7) | ~r2_hidden(X6,k1_zfmisc_1(sK1))) ) | ~spl5_4),
% 1.51/0.58    inference(resolution,[],[f113,f79])).
% 1.51/0.58  fof(f79,plain,(
% 1.51/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.51/0.58    inference(equality_resolution,[],[f56])).
% 1.51/0.58  fof(f56,plain,(
% 1.51/0.58    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.51/0.58    inference(cnf_transformation,[],[f33])).
% 1.51/0.58  fof(f113,plain,(
% 1.51/0.58    ( ! [X4,X5] : (r2_hidden(X5,k4_xboole_0(k4_xboole_0(X4,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1))) | r2_hidden(X5,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | ~r2_hidden(X5,X4)) ) | ~spl5_4),
% 1.51/0.58    inference(superposition,[],[f78,f103])).
% 1.51/0.58  fof(f103,plain,(
% 1.51/0.58    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1)) = k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))) ) | ~spl5_4),
% 1.51/0.58    inference(superposition,[],[f70,f101])).
% 1.51/0.58  fof(f101,plain,(
% 1.51/0.58    k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~spl5_4),
% 1.51/0.58    inference(avatar_component_clause,[],[f99])).
% 1.51/0.58  fof(f70,plain,(
% 1.51/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 1.51/0.58    inference(definition_unfolding,[],[f54,f61])).
% 1.51/0.58  fof(f54,plain,(
% 1.51/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.51/0.58    inference(cnf_transformation,[],[f4])).
% 1.51/0.58  fof(f4,axiom,(
% 1.51/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.51/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.51/0.58  fof(f225,plain,(
% 1.51/0.58    ~r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | spl5_15),
% 1.51/0.58    inference(avatar_component_clause,[],[f223])).
% 1.51/0.58  fof(f230,plain,(
% 1.51/0.58    ~spl5_15 | spl5_16 | ~spl5_14),
% 1.51/0.58    inference(avatar_split_clause,[],[f213,f209,f227,f223])).
% 1.51/0.58  fof(f209,plain,(
% 1.51/0.58    spl5_14 <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1)),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.51/0.58  fof(f213,plain,(
% 1.51/0.58    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~spl5_14),
% 1.51/0.58    inference(resolution,[],[f211,f43])).
% 1.51/0.58  fof(f211,plain,(
% 1.51/0.58    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1) | ~spl5_14),
% 1.51/0.58    inference(avatar_component_clause,[],[f209])).
% 1.51/0.58  fof(f212,plain,(
% 1.51/0.58    spl5_14 | ~spl5_12),
% 1.51/0.58    inference(avatar_split_clause,[],[f207,f200,f209])).
% 1.51/0.58  fof(f200,plain,(
% 1.51/0.58    spl5_12 <=> r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1))),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.51/0.58  fof(f207,plain,(
% 1.51/0.58    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1) | ~spl5_12),
% 1.51/0.58    inference(resolution,[],[f202,f77])).
% 1.51/0.58  fof(f202,plain,(
% 1.51/0.58    r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl5_12),
% 1.51/0.58    inference(avatar_component_clause,[],[f200])).
% 1.51/0.58  fof(f206,plain,(
% 1.51/0.58    spl5_12 | spl5_13 | ~spl5_4),
% 1.51/0.58    inference(avatar_split_clause,[],[f137,f99,f204,f200])).
% 1.51/0.58  fof(f137,plain,(
% 1.51/0.58    ( ! [X1] : (~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0))) | r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1))) ) | ~spl5_4),
% 1.51/0.58    inference(resolution,[],[f131,f72])).
% 1.51/0.58  fof(f131,plain,(
% 1.51/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(sK0))) | r2_hidden(X0,k1_zfmisc_1(sK1))) ) | ~spl5_4),
% 1.51/0.58    inference(resolution,[],[f118,f76])).
% 1.51/0.58  fof(f118,plain,(
% 1.51/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | r2_hidden(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(sK0)))) ) | ~spl5_4),
% 1.51/0.58    inference(resolution,[],[f112,f78])).
% 1.51/0.58  fof(f112,plain,(
% 1.51/0.58    ( ! [X2,X3] : (~r2_hidden(X3,k4_xboole_0(k4_xboole_0(X2,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1))) | ~r2_hidden(X3,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))) ) | ~spl5_4),
% 1.51/0.58    inference(superposition,[],[f79,f103])).
% 1.51/0.58  fof(f102,plain,(
% 1.51/0.58    spl5_4),
% 1.51/0.58    inference(avatar_split_clause,[],[f63,f99])).
% 1.51/0.58  fof(f63,plain,(
% 1.51/0.58    k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 1.51/0.58    inference(definition_unfolding,[],[f34,f61,f61])).
% 1.51/0.58  fof(f34,plain,(
% 1.51/0.58    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))),
% 1.51/0.58    inference(cnf_transformation,[],[f18])).
% 1.51/0.58  fof(f18,plain,(
% 1.51/0.58    ~r3_xboole_0(sK0,sK1) & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))),
% 1.51/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 1.51/0.58  fof(f17,plain,(
% 1.51/0.58    ? [X0,X1] : (~r3_xboole_0(X0,X1) & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))) => (~r3_xboole_0(sK0,sK1) & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 1.51/0.58    introduced(choice_axiom,[])).
% 1.51/0.58  fof(f15,plain,(
% 1.51/0.58    ? [X0,X1] : (~r3_xboole_0(X0,X1) & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 1.51/0.58    inference(ennf_transformation,[],[f13])).
% 1.51/0.58  fof(f13,negated_conjecture,(
% 1.51/0.58    ~! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 1.51/0.58    inference(negated_conjecture,[],[f12])).
% 1.51/0.58  fof(f12,conjecture,(
% 1.51/0.58    ! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 1.51/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_zfmisc_1)).
% 1.51/0.58  fof(f97,plain,(
% 1.51/0.58    ~spl5_3 | spl5_1),
% 1.51/0.58    inference(avatar_split_clause,[],[f87,f82,f94])).
% 1.51/0.58  fof(f94,plain,(
% 1.51/0.58    spl5_3 <=> r1_tarski(sK1,sK0)),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.51/0.58  fof(f82,plain,(
% 1.51/0.58    spl5_1 <=> r3_xboole_0(sK0,sK1)),
% 1.51/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.51/0.58  fof(f87,plain,(
% 1.51/0.58    ~r1_tarski(sK1,sK0) | spl5_1),
% 1.51/0.58    inference(resolution,[],[f84,f45])).
% 1.51/0.58  fof(f45,plain,(
% 1.51/0.58    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.51/0.58    inference(cnf_transformation,[],[f16])).
% 1.51/0.58  fof(f16,plain,(
% 1.51/0.58    ! [X0,X1] : (r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1)))),
% 1.51/0.58    inference(ennf_transformation,[],[f14])).
% 1.51/0.58  fof(f14,plain,(
% 1.51/0.58    ! [X0,X1] : ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) => r3_xboole_0(X0,X1))),
% 1.51/0.58    inference(unused_predicate_definition_removal,[],[f3])).
% 1.51/0.58  fof(f3,axiom,(
% 1.51/0.58    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 1.51/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).
% 1.51/0.58  fof(f84,plain,(
% 1.51/0.58    ~r3_xboole_0(sK0,sK1) | spl5_1),
% 1.51/0.58    inference(avatar_component_clause,[],[f82])).
% 1.51/0.58  fof(f92,plain,(
% 1.51/0.58    ~spl5_2 | spl5_1),
% 1.51/0.58    inference(avatar_split_clause,[],[f86,f82,f89])).
% 1.51/0.58  fof(f86,plain,(
% 1.51/0.58    ~r1_tarski(sK0,sK1) | spl5_1),
% 1.51/0.58    inference(resolution,[],[f84,f44])).
% 1.51/0.58  fof(f44,plain,(
% 1.51/0.58    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.51/0.58    inference(cnf_transformation,[],[f16])).
% 1.51/0.58  fof(f85,plain,(
% 1.51/0.58    ~spl5_1),
% 1.51/0.58    inference(avatar_split_clause,[],[f35,f82])).
% 1.51/0.58  fof(f35,plain,(
% 1.51/0.58    ~r3_xboole_0(sK0,sK1)),
% 1.51/0.58    inference(cnf_transformation,[],[f18])).
% 1.51/0.58  % SZS output end Proof for theBenchmark
% 1.51/0.58  % (17079)------------------------------
% 1.51/0.58  % (17079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (17079)Termination reason: Refutation
% 1.51/0.58  
% 1.51/0.58  % (17079)Memory used [KB]: 10874
% 1.51/0.58  % (17079)Time elapsed: 0.145 s
% 1.51/0.58  % (17079)------------------------------
% 1.51/0.58  % (17079)------------------------------
% 1.51/0.58  % (17068)Success in time 0.239 s
%------------------------------------------------------------------------------
