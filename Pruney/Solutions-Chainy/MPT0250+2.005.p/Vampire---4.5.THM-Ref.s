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
% DateTime   : Thu Dec  3 12:38:20 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 192 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :   20
%              Number of atoms          :  301 ( 777 expanded)
%              Number of equality atoms :  105 ( 279 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f503,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f119,f185,f502])).

fof(f502,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | spl4_1
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f72,f447,f447,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k4_xboole_0(X0,X1))
      | r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f50,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f447,plain,
    ( ! [X0] : ~ r2_hidden(sK0,X0)
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f446,f102])).

% (8429)Refutation not found, incomplete strategy% (8429)------------------------------
% (8429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8429)Termination reason: Refutation not found, incomplete strategy

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X2,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f54,f68])).

% (8429)Memory used [KB]: 6268
% (8429)Time elapsed: 0.139 s
fof(f68,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

% (8429)------------------------------
% (8429)------------------------------
fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f446,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(sK0,k4_xboole_0(sK1,X0)) )
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f443,f83])).

fof(f83,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f443,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(sK0,sK1)
        | r2_hidden(sK0,k4_xboole_0(sK1,X0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f439,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | r2_hidden(X2,X0)
      | r2_hidden(X2,k4_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f51,f67])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f439,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k3_xboole_0(sK1,X0))
        | ~ r2_hidden(sK0,X0) )
    | ~ spl4_4 ),
    inference(superposition,[],[f325,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f325,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k3_xboole_0(X0,sK1))
        | ~ r2_hidden(sK0,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f307,f130])).

fof(f307,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f280,f68])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK1)
        | ~ r2_hidden(sK0,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f259,f105])).

fof(f105,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f99,f63])).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f99,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f76,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f76,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f259,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_tarski(sK0))
        | ~ r1_xboole_0(X0,sK1)
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f203,f54])).

fof(f203,plain,
    ( ! [X1] :
        ( r1_xboole_0(X1,k1_tarski(sK0))
        | ~ r1_xboole_0(X1,sK1) )
    | ~ spl4_4 ),
    inference(superposition,[],[f60,f118])).

fof(f118,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_4
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

% (8409)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f72,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f185,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f170,f58])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f170,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK0)))
    | spl4_3 ),
    inference(backward_demodulation,[],[f114,f168])).

fof(f168,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f95,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f95,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f62,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

% (8420)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f114,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_3
  <=> r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f119,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f108,f86,f116,f112])).

fof(f86,plain,
    ( spl4_2
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f108,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f57,f88])).

fof(f88,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f89,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f38,f86])).

fof(f38,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f84,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:13:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.48  % (8408)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (8432)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (8424)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % (8403)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (8419)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (8415)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.51  % (8415)Refutation not found, incomplete strategy% (8415)------------------------------
% 0.20/0.51  % (8415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8415)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8415)Memory used [KB]: 10618
% 0.20/0.51  % (8415)Time elapsed: 0.117 s
% 0.20/0.51  % (8415)------------------------------
% 0.20/0.51  % (8415)------------------------------
% 0.20/0.51  % (8416)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (8432)Refutation not found, incomplete strategy% (8432)------------------------------
% 0.20/0.51  % (8432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8432)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8432)Memory used [KB]: 1663
% 0.20/0.51  % (8432)Time elapsed: 0.002 s
% 0.20/0.51  % (8432)------------------------------
% 0.20/0.51  % (8432)------------------------------
% 0.20/0.52  % (8410)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.32/0.52  % (8419)Refutation not found, incomplete strategy% (8419)------------------------------
% 1.32/0.52  % (8419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.52  % (8411)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.52  % (8419)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.52  
% 1.32/0.52  % (8419)Memory used [KB]: 10618
% 1.32/0.52  % (8419)Time elapsed: 0.118 s
% 1.32/0.52  % (8419)------------------------------
% 1.32/0.52  % (8419)------------------------------
% 1.32/0.52  % (8404)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.52  % (8405)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.52  % (8406)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.32/0.52  % (8404)Refutation not found, incomplete strategy% (8404)------------------------------
% 1.32/0.52  % (8404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.52  % (8404)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.52  
% 1.32/0.52  % (8404)Memory used [KB]: 1663
% 1.32/0.52  % (8404)Time elapsed: 0.124 s
% 1.32/0.52  % (8404)------------------------------
% 1.32/0.52  % (8404)------------------------------
% 1.32/0.52  % (8427)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.52  % (8407)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.32/0.53  % (8428)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.32/0.53  % (8426)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.32/0.53  % (8431)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.53  % (8429)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.32/0.53  % (8430)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.53  % (8424)Refutation found. Thanks to Tanya!
% 1.32/0.53  % SZS status Theorem for theBenchmark
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  fof(f503,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(avatar_sat_refutation,[],[f84,f89,f119,f185,f502])).
% 1.32/0.53  fof(f502,plain,(
% 1.32/0.53    spl4_1 | ~spl4_4),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f480])).
% 1.32/0.53  fof(f480,plain,(
% 1.32/0.53    $false | (spl4_1 | ~spl4_4)),
% 1.32/0.53    inference(unit_resulting_resolution,[],[f72,f447,f447,f130])).
% 1.32/0.53  fof(f130,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,k4_xboole_0(X0,X1)) | r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.32/0.53    inference(superposition,[],[f50,f67])).
% 1.32/0.53  fof(f67,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f5])).
% 1.32/0.53  fof(f5,axiom,(
% 1.32/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.32/0.53  fof(f50,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f33])).
% 1.32/0.53  fof(f33,plain,(
% 1.32/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.32/0.53    inference(nnf_transformation,[],[f23])).
% 1.32/0.53  fof(f23,plain,(
% 1.32/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.32/0.53    inference(ennf_transformation,[],[f2])).
% 1.32/0.53  fof(f2,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.32/0.53  fof(f447,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(sK0,X0)) ) | (spl4_1 | ~spl4_4)),
% 1.32/0.53    inference(subsumption_resolution,[],[f446,f102])).
% 1.32/0.53  % (8429)Refutation not found, incomplete strategy% (8429)------------------------------
% 1.32/0.53  % (8429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (8429)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  fof(f102,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X2,X1)) | ~r2_hidden(X0,X1)) )),
% 1.32/0.53    inference(resolution,[],[f54,f68])).
% 1.32/0.53  % (8429)Memory used [KB]: 6268
% 1.32/0.53  % (8429)Time elapsed: 0.139 s
% 1.32/0.53  fof(f68,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f7])).
% 1.32/0.53  % (8429)------------------------------
% 1.32/0.53  % (8429)------------------------------
% 1.32/0.53  fof(f7,axiom,(
% 1.32/0.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.32/0.53  fof(f54,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f35])).
% 1.32/0.53  fof(f35,plain,(
% 1.32/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f34])).
% 1.32/0.53  fof(f34,plain,(
% 1.32/0.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f24,plain,(
% 1.32/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(ennf_transformation,[],[f20])).
% 1.32/0.53  fof(f20,plain,(
% 1.32/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(rectify,[],[f3])).
% 1.32/0.53  fof(f3,axiom,(
% 1.32/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.32/0.53  fof(f446,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(sK0,X0) | r2_hidden(sK0,k4_xboole_0(sK1,X0))) ) | (spl4_1 | ~spl4_4)),
% 1.32/0.53    inference(subsumption_resolution,[],[f443,f83])).
% 1.32/0.53  fof(f83,plain,(
% 1.32/0.53    ~r2_hidden(sK0,sK1) | spl4_1),
% 1.32/0.53    inference(avatar_component_clause,[],[f81])).
% 1.32/0.53  fof(f81,plain,(
% 1.32/0.53    spl4_1 <=> r2_hidden(sK0,sK1)),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.32/0.53  fof(f443,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(sK0,X0) | r2_hidden(sK0,sK1) | r2_hidden(sK0,k4_xboole_0(sK1,X0))) ) | ~spl4_4),
% 1.32/0.53    inference(resolution,[],[f439,f138])).
% 1.32/0.53  fof(f138,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | r2_hidden(X2,X0) | r2_hidden(X2,k4_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(superposition,[],[f51,f67])).
% 1.32/0.53  fof(f51,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f33])).
% 1.32/0.53  fof(f439,plain,(
% 1.32/0.53    ( ! [X0] : (r2_hidden(sK0,k3_xboole_0(sK1,X0)) | ~r2_hidden(sK0,X0)) ) | ~spl4_4),
% 1.32/0.53    inference(superposition,[],[f325,f70])).
% 1.32/0.53  fof(f70,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f1])).
% 1.32/0.53  fof(f1,axiom,(
% 1.32/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.32/0.53  fof(f325,plain,(
% 1.32/0.53    ( ! [X0] : (r2_hidden(sK0,k3_xboole_0(X0,sK1)) | ~r2_hidden(sK0,X0)) ) | ~spl4_4),
% 1.32/0.53    inference(resolution,[],[f307,f130])).
% 1.32/0.53  fof(f307,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,sK1))) ) | ~spl4_4),
% 1.32/0.53    inference(resolution,[],[f280,f68])).
% 1.32/0.53  fof(f280,plain,(
% 1.32/0.53    ( ! [X0] : (~r1_xboole_0(X0,sK1) | ~r2_hidden(sK0,X0)) ) | ~spl4_4),
% 1.32/0.53    inference(resolution,[],[f259,f105])).
% 1.32/0.53  fof(f105,plain,(
% 1.32/0.53    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.32/0.53    inference(superposition,[],[f99,f63])).
% 1.32/0.53  fof(f63,plain,(
% 1.32/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f11])).
% 1.32/0.53  fof(f11,axiom,(
% 1.32/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.53  fof(f99,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.32/0.53    inference(superposition,[],[f76,f64])).
% 1.32/0.53  fof(f64,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f12])).
% 1.32/0.53  fof(f12,axiom,(
% 1.32/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.53  fof(f76,plain,(
% 1.32/0.53    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 1.32/0.53    inference(equality_resolution,[],[f75])).
% 1.32/0.53  fof(f75,plain,(
% 1.32/0.53    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 1.32/0.53    inference(equality_resolution,[],[f41])).
% 1.32/0.53  fof(f41,plain,(
% 1.32/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.32/0.53    inference(cnf_transformation,[],[f32])).
% 1.32/0.53  fof(f32,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 1.32/0.53  fof(f31,plain,(
% 1.32/0.53    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f30,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.32/0.53    inference(rectify,[],[f29])).
% 1.32/0.53  fof(f29,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.32/0.53    inference(flattening,[],[f28])).
% 1.32/0.53  fof(f28,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.32/0.53    inference(nnf_transformation,[],[f22])).
% 1.32/0.53  fof(f22,plain,(
% 1.32/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.32/0.53    inference(ennf_transformation,[],[f10])).
% 1.32/0.53  fof(f10,axiom,(
% 1.32/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.32/0.53  fof(f259,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(sK0)) | ~r1_xboole_0(X0,sK1) | ~r2_hidden(X1,X0)) ) | ~spl4_4),
% 1.32/0.53    inference(resolution,[],[f203,f54])).
% 1.32/0.53  fof(f203,plain,(
% 1.32/0.53    ( ! [X1] : (r1_xboole_0(X1,k1_tarski(sK0)) | ~r1_xboole_0(X1,sK1)) ) | ~spl4_4),
% 1.32/0.53    inference(superposition,[],[f60,f118])).
% 1.32/0.53  fof(f118,plain,(
% 1.32/0.53    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | ~spl4_4),
% 1.32/0.53    inference(avatar_component_clause,[],[f116])).
% 1.32/0.53  fof(f116,plain,(
% 1.32/0.53    spl4_4 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.32/0.53  fof(f60,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f25])).
% 1.32/0.53  fof(f25,plain,(
% 1.32/0.53    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.32/0.53    inference(ennf_transformation,[],[f6])).
% 1.32/0.53  % (8409)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.53  fof(f6,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.32/0.53  fof(f72,plain,(
% 1.32/0.53    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 1.32/0.53    inference(equality_resolution,[],[f71])).
% 1.32/0.53  fof(f71,plain,(
% 1.32/0.53    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 1.32/0.53    inference(equality_resolution,[],[f43])).
% 1.32/0.53  fof(f43,plain,(
% 1.32/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.32/0.53    inference(cnf_transformation,[],[f32])).
% 1.32/0.53  fof(f185,plain,(
% 1.32/0.53    spl4_3),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f184])).
% 1.32/0.53  fof(f184,plain,(
% 1.32/0.53    $false | spl4_3),
% 1.32/0.53    inference(subsumption_resolution,[],[f170,f58])).
% 1.32/0.53  fof(f58,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f8])).
% 1.32/0.53  fof(f8,axiom,(
% 1.32/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.32/0.53  fof(f170,plain,(
% 1.32/0.53    ~r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK0))) | spl4_3),
% 1.32/0.53    inference(backward_demodulation,[],[f114,f168])).
% 1.32/0.53  fof(f168,plain,(
% 1.32/0.53    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.32/0.53    inference(superposition,[],[f95,f62])).
% 1.32/0.53  fof(f62,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f17])).
% 1.32/0.53  fof(f17,axiom,(
% 1.32/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.32/0.53  fof(f95,plain,(
% 1.32/0.53    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 1.32/0.53    inference(superposition,[],[f62,f65])).
% 1.32/0.53  fof(f65,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f9])).
% 1.32/0.53  fof(f9,axiom,(
% 1.32/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.32/0.53  % (8420)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.32/0.53  fof(f114,plain,(
% 1.32/0.53    ~r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) | spl4_3),
% 1.32/0.53    inference(avatar_component_clause,[],[f112])).
% 1.32/0.53  fof(f112,plain,(
% 1.32/0.53    spl4_3 <=> r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),sK1))),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.32/0.53  fof(f119,plain,(
% 1.32/0.53    ~spl4_3 | spl4_4 | ~spl4_2),
% 1.32/0.53    inference(avatar_split_clause,[],[f108,f86,f116,f112])).
% 1.32/0.53  fof(f86,plain,(
% 1.32/0.53    spl4_2 <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.32/0.53  fof(f108,plain,(
% 1.32/0.53    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | ~r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) | ~spl4_2),
% 1.32/0.53    inference(resolution,[],[f57,f88])).
% 1.32/0.53  fof(f88,plain,(
% 1.32/0.53    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) | ~spl4_2),
% 1.32/0.53    inference(avatar_component_clause,[],[f86])).
% 1.32/0.53  fof(f57,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f37])).
% 1.32/0.53  fof(f37,plain,(
% 1.32/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.53    inference(flattening,[],[f36])).
% 1.32/0.53  fof(f36,plain,(
% 1.32/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.53    inference(nnf_transformation,[],[f4])).
% 1.32/0.53  fof(f4,axiom,(
% 1.32/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.32/0.53  fof(f89,plain,(
% 1.32/0.53    spl4_2),
% 1.32/0.53    inference(avatar_split_clause,[],[f38,f86])).
% 1.32/0.53  fof(f38,plain,(
% 1.32/0.53    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 1.32/0.53    inference(cnf_transformation,[],[f27])).
% 1.32/0.53  fof(f27,plain,(
% 1.32/0.53    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f21,plain,(
% 1.32/0.53    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f19])).
% 1.32/0.53  fof(f19,negated_conjecture,(
% 1.32/0.53    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 1.32/0.53    inference(negated_conjecture,[],[f18])).
% 1.32/0.53  fof(f18,conjecture,(
% 1.32/0.53    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 1.32/0.53  fof(f84,plain,(
% 1.32/0.53    ~spl4_1),
% 1.32/0.53    inference(avatar_split_clause,[],[f39,f81])).
% 1.32/0.53  fof(f39,plain,(
% 1.32/0.53    ~r2_hidden(sK0,sK1)),
% 1.32/0.53    inference(cnf_transformation,[],[f27])).
% 1.32/0.53  % SZS output end Proof for theBenchmark
% 1.32/0.53  % (8424)------------------------------
% 1.32/0.53  % (8424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (8424)Termination reason: Refutation
% 1.32/0.53  
% 1.32/0.53  % (8424)Memory used [KB]: 6652
% 1.32/0.53  % (8424)Time elapsed: 0.140 s
% 1.32/0.53  % (8424)------------------------------
% 1.32/0.53  % (8424)------------------------------
% 1.32/0.53  % (8402)Success in time 0.184 s
%------------------------------------------------------------------------------
