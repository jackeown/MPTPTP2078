%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:59 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 114 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  307 ( 525 expanded)
%              Number of equality atoms :  133 ( 246 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f111,f151,f158])).

fof(f158,plain,
    ( spl5_1
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl5_1
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f105,f105,f105,f148,f98])).

fof(f98,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

% (6784)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f28,plain,(
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
    inference(nnf_transformation,[],[f19])).

% (6783)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f148,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl5_5
  <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f105,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f151,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f144,f108,f146])).

fof(f108,plain,
    ( spl5_2
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f144,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f141,f97])).

fof(f97,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f141,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(X2,k2_enumset1(sK1,sK1,sK1,sK1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f139,f110])).

fof(f110,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f132,f87])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
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

fof(f132,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tarski(X6,X7)
      | ~ r2_hidden(X4,X6)
      | ~ r1_tarski(X6,X5)
      | ~ r2_hidden(X4,X7)
      | r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f130,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(X0,X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f100,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f59,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

% (6766)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f36,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

% (6783)Refutation not found, incomplete strategy% (6783)------------------------------
% (6783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6783)Termination reason: Refutation not found, incomplete strategy

% (6783)Memory used [KB]: 6268
% (6783)Time elapsed: 0.127 s
% (6783)------------------------------
% (6783)------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_xboole_0(X0,X0))
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f99,f43])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f60,f49])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

% (6786)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f111,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f68,f108])).

fof(f68,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f38,f67,f67])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

% (6760)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f106,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f39,f103])).

fof(f39,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:53:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (6764)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (6779)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (6771)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (6780)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (6771)Refutation not found, incomplete strategy% (6771)------------------------------
% 0.21/0.51  % (6771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6771)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6771)Memory used [KB]: 1791
% 0.21/0.51  % (6771)Time elapsed: 0.054 s
% 0.21/0.51  % (6771)------------------------------
% 0.21/0.51  % (6771)------------------------------
% 1.23/0.51  % (6763)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.52  % (6772)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.23/0.52  % (6761)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.23/0.52  % (6759)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.23/0.53  % (6758)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.53  % (6762)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.23/0.54  % (6780)Refutation found. Thanks to Tanya!
% 1.23/0.54  % SZS status Theorem for theBenchmark
% 1.43/0.54  % (6785)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.43/0.54  % SZS output start Proof for theBenchmark
% 1.43/0.54  fof(f159,plain,(
% 1.43/0.54    $false),
% 1.43/0.54    inference(avatar_sat_refutation,[],[f106,f111,f151,f158])).
% 1.43/0.54  fof(f158,plain,(
% 1.43/0.54    spl5_1 | ~spl5_5),
% 1.43/0.54    inference(avatar_contradiction_clause,[],[f153])).
% 1.43/0.54  fof(f153,plain,(
% 1.43/0.54    $false | (spl5_1 | ~spl5_5)),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f105,f105,f105,f148,f98])).
% 1.43/0.54  fof(f98,plain,(
% 1.43/0.54    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.43/0.54    inference(equality_resolution,[],[f80])).
% 1.43/0.54  fof(f80,plain,(
% 1.43/0.54    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.43/0.54    inference(definition_unfolding,[],[f50,f65])).
% 1.43/0.54  fof(f65,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f10])).
% 1.43/0.54  fof(f10,axiom,(
% 1.43/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.43/0.54  fof(f50,plain,(
% 1.43/0.54    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.43/0.54    inference(cnf_transformation,[],[f32])).
% 1.43/0.54  fof(f32,plain,(
% 1.43/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.43/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 1.43/0.54  fof(f31,plain,(
% 1.43/0.54    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.43/0.54    introduced(choice_axiom,[])).
% 1.43/0.54  fof(f30,plain,(
% 1.43/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.43/0.54    inference(rectify,[],[f29])).
% 1.43/0.54  fof(f29,plain,(
% 1.43/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.43/0.54    inference(flattening,[],[f28])).
% 1.43/0.54  % (6784)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.54  fof(f28,plain,(
% 1.43/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.43/0.54    inference(nnf_transformation,[],[f19])).
% 1.43/0.54  % (6783)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.54  fof(f19,plain,(
% 1.43/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.43/0.54    inference(ennf_transformation,[],[f6])).
% 1.43/0.54  fof(f6,axiom,(
% 1.43/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.43/0.54  fof(f148,plain,(
% 1.43/0.54    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_5),
% 1.43/0.54    inference(avatar_component_clause,[],[f146])).
% 1.43/0.54  fof(f146,plain,(
% 1.43/0.54    spl5_5 <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.43/0.54  fof(f105,plain,(
% 1.43/0.54    sK0 != sK1 | spl5_1),
% 1.43/0.54    inference(avatar_component_clause,[],[f103])).
% 1.43/0.54  fof(f103,plain,(
% 1.43/0.54    spl5_1 <=> sK0 = sK1),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.43/0.54  fof(f151,plain,(
% 1.43/0.54    spl5_5 | ~spl5_2),
% 1.43/0.54    inference(avatar_split_clause,[],[f144,f108,f146])).
% 1.43/0.54  fof(f108,plain,(
% 1.43/0.54    spl5_2 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.43/0.54  fof(f144,plain,(
% 1.43/0.54    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_2),
% 1.43/0.54    inference(resolution,[],[f141,f97])).
% 1.43/0.54  fof(f97,plain,(
% 1.43/0.54    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 1.43/0.54    inference(equality_resolution,[],[f96])).
% 1.43/0.54  fof(f96,plain,(
% 1.43/0.54    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 1.43/0.54    inference(equality_resolution,[],[f79])).
% 1.43/0.54  fof(f79,plain,(
% 1.43/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.43/0.54    inference(definition_unfolding,[],[f51,f65])).
% 1.43/0.54  fof(f51,plain,(
% 1.43/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.43/0.54    inference(cnf_transformation,[],[f32])).
% 1.43/0.54  fof(f141,plain,(
% 1.43/0.54    ( ! [X2] : (~r2_hidden(X2,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(X2,k2_enumset1(sK1,sK1,sK1,sK1))) ) | ~spl5_2),
% 1.43/0.54    inference(resolution,[],[f139,f110])).
% 1.43/0.54  fof(f110,plain,(
% 1.43/0.54    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_2),
% 1.43/0.54    inference(avatar_component_clause,[],[f108])).
% 1.43/0.54  fof(f139,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.43/0.54    inference(duplicate_literal_removal,[],[f137])).
% 1.43/0.54  fof(f137,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.43/0.54    inference(resolution,[],[f132,f87])).
% 1.43/0.54  fof(f87,plain,(
% 1.43/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.43/0.54    inference(equality_resolution,[],[f41])).
% 1.43/0.54  fof(f41,plain,(
% 1.43/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.43/0.54    inference(cnf_transformation,[],[f23])).
% 1.43/0.54  fof(f23,plain,(
% 1.43/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.54    inference(flattening,[],[f22])).
% 1.43/0.54  fof(f22,plain,(
% 1.43/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.54    inference(nnf_transformation,[],[f3])).
% 1.43/0.54  fof(f3,axiom,(
% 1.43/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.43/0.54  fof(f132,plain,(
% 1.43/0.54    ( ! [X6,X4,X7,X5] : (~r1_tarski(X6,X7) | ~r2_hidden(X4,X6) | ~r1_tarski(X6,X5) | ~r2_hidden(X4,X7) | r2_hidden(X4,X5)) )),
% 1.43/0.54    inference(resolution,[],[f130,f126])).
% 1.43/0.54  fof(f126,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(X0,X0)) | ~r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.43/0.54    inference(superposition,[],[f100,f43])).
% 1.43/0.54  fof(f43,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f18])).
% 1.43/0.54  fof(f18,plain,(
% 1.43/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.43/0.54    inference(ennf_transformation,[],[f5])).
% 1.43/0.54  fof(f5,axiom,(
% 1.43/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.43/0.54  fof(f100,plain,(
% 1.43/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.43/0.54    inference(equality_resolution,[],[f85])).
% 1.43/0.54  fof(f85,plain,(
% 1.43/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.43/0.54    inference(definition_unfolding,[],[f59,f49])).
% 1.43/0.54  fof(f49,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f4])).
% 1.43/0.54  fof(f4,axiom,(
% 1.43/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.43/0.54  fof(f59,plain,(
% 1.43/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.43/0.54    inference(cnf_transformation,[],[f37])).
% 1.43/0.54  fof(f37,plain,(
% 1.43/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.43/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 1.43/0.54  % (6766)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.54  fof(f36,plain,(
% 1.43/0.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.43/0.54    introduced(choice_axiom,[])).
% 1.43/0.54  fof(f35,plain,(
% 1.43/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.43/0.54    inference(rectify,[],[f34])).
% 1.43/0.54  fof(f34,plain,(
% 1.43/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.43/0.54    inference(flattening,[],[f33])).
% 1.43/0.54  fof(f33,plain,(
% 1.43/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.43/0.54    inference(nnf_transformation,[],[f1])).
% 1.43/0.54  % (6783)Refutation not found, incomplete strategy% (6783)------------------------------
% 1.43/0.54  % (6783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (6783)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (6783)Memory used [KB]: 6268
% 1.43/0.54  % (6783)Time elapsed: 0.127 s
% 1.43/0.54  % (6783)------------------------------
% 1.43/0.54  % (6783)------------------------------
% 1.43/0.54  fof(f1,axiom,(
% 1.43/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.43/0.54  fof(f130,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_xboole_0(X0,X0)) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.43/0.54    inference(superposition,[],[f99,f43])).
% 1.43/0.54  fof(f99,plain,(
% 1.43/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.43/0.54    inference(equality_resolution,[],[f84])).
% 1.43/0.54  fof(f84,plain,(
% 1.43/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.43/0.54    inference(definition_unfolding,[],[f60,f49])).
% 1.43/0.54  fof(f60,plain,(
% 1.43/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.43/0.54    inference(cnf_transformation,[],[f37])).
% 1.43/0.54  % (6786)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.54  fof(f111,plain,(
% 1.43/0.54    spl5_2),
% 1.43/0.54    inference(avatar_split_clause,[],[f68,f108])).
% 1.43/0.54  fof(f68,plain,(
% 1.43/0.54    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.43/0.54    inference(definition_unfolding,[],[f38,f67,f67])).
% 1.43/0.54  fof(f67,plain,(
% 1.43/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.43/0.54    inference(definition_unfolding,[],[f48,f66])).
% 1.43/0.54  fof(f66,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.43/0.54    inference(definition_unfolding,[],[f64,f65])).
% 1.43/0.54  fof(f64,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f9])).
% 1.43/0.54  fof(f9,axiom,(
% 1.43/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.43/0.54  % (6760)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.43/0.54  fof(f48,plain,(
% 1.43/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f8])).
% 1.43/0.54  fof(f8,axiom,(
% 1.43/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.43/0.54  fof(f38,plain,(
% 1.43/0.54    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.43/0.54    inference(cnf_transformation,[],[f21])).
% 1.43/0.54  fof(f21,plain,(
% 1.43/0.54    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.43/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f20])).
% 1.43/0.54  fof(f20,plain,(
% 1.43/0.54    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.43/0.54    introduced(choice_axiom,[])).
% 1.43/0.54  fof(f17,plain,(
% 1.43/0.54    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.43/0.54    inference(ennf_transformation,[],[f16])).
% 1.43/0.54  fof(f16,negated_conjecture,(
% 1.43/0.54    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.43/0.54    inference(negated_conjecture,[],[f15])).
% 1.43/0.54  fof(f15,conjecture,(
% 1.43/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.43/0.54  fof(f106,plain,(
% 1.43/0.54    ~spl5_1),
% 1.43/0.54    inference(avatar_split_clause,[],[f39,f103])).
% 1.43/0.54  fof(f39,plain,(
% 1.43/0.54    sK0 != sK1),
% 1.43/0.54    inference(cnf_transformation,[],[f21])).
% 1.43/0.54  % SZS output end Proof for theBenchmark
% 1.43/0.54  % (6780)------------------------------
% 1.43/0.54  % (6780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (6780)Termination reason: Refutation
% 1.43/0.54  
% 1.43/0.54  % (6780)Memory used [KB]: 10746
% 1.43/0.54  % (6780)Time elapsed: 0.129 s
% 1.43/0.54  % (6780)------------------------------
% 1.43/0.54  % (6780)------------------------------
% 1.43/0.54  % (6786)Refutation not found, incomplete strategy% (6786)------------------------------
% 1.43/0.54  % (6786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (6786)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (6786)Memory used [KB]: 1663
% 1.43/0.54  % (6786)Time elapsed: 0.138 s
% 1.43/0.54  % (6786)------------------------------
% 1.43/0.54  % (6786)------------------------------
% 1.43/0.54  % (6756)Success in time 0.18 s
%------------------------------------------------------------------------------
