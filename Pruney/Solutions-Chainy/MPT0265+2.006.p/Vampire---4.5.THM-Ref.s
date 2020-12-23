%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:26 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 182 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  349 (1013 expanded)
%              Number of equality atoms :  133 ( 415 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1372,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f1108,f1110,f1209,f1295,f1346,f1348])).

fof(f1348,plain,
    ( ~ spl6_2
    | spl6_27
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f1319,f1206,f1202,f64])).

fof(f64,plain,
    ( spl6_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1202,plain,
    ( spl6_27
  <=> sK0 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1206,plain,
    ( spl6_28
  <=> sK2 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f1319,plain,
    ( sK0 != sK2
    | spl6_27
    | ~ spl6_28 ),
    inference(superposition,[],[f1203,f1208])).

fof(f1208,plain,
    ( sK2 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f1206])).

fof(f1203,plain,
    ( sK0 != sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f1346,plain,
    ( spl6_1
    | spl6_13
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f1345,f1206,f257,f60])).

fof(f60,plain,
    ( spl6_1
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f257,plain,
    ( spl6_13
  <=> r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f1345,plain,
    ( r2_hidden(sK2,sK1)
    | spl6_13
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1344,f1321])).

fof(f1321,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK0))
    | spl6_13
    | ~ spl6_28 ),
    inference(superposition,[],[f258,f1208])).

fof(f258,plain,
    ( ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f257])).

fof(f1344,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK2,k1_tarski(sK0))
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1325,f29])).

fof(f29,plain,(
    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    & ( sK0 = sK2
      | ~ r2_hidden(sK2,sK1) )
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
      & ( sK0 = sK2
        | ~ r2_hidden(sK2,sK1) )
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f1325,plain,
    ( r2_hidden(sK2,sK1)
    | k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    | r2_hidden(sK2,k1_tarski(sK0))
    | ~ spl6_28 ),
    inference(superposition,[],[f34,f1208])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1295,plain,(
    ~ spl6_27 ),
    inference(avatar_contradiction_clause,[],[f1294])).

fof(f1294,plain,
    ( $false
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f1293,f54])).

fof(f54,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f1293,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK2))
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f1292,f27])).

fof(f27,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f1292,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK2))
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f1291,f29])).

fof(f1291,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK2))
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f1275,f57])).

fof(f57,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1275,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK2))
    | ~ spl6_27 ),
    inference(superposition,[],[f35,f1204])).

fof(f1204,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1209,plain,
    ( spl6_27
    | spl6_28
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f1193,f326,f1206,f1202])).

fof(f326,plain,
    ( spl6_15
  <=> r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k2_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1193,plain,
    ( sK2 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0))
    | sK0 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0))
    | ~ spl6_15 ),
    inference(resolution,[],[f327,f55])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f327,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k2_tarski(sK0,sK2))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f326])).

fof(f1110,plain,
    ( spl6_13
    | spl6_15 ),
    inference(avatar_split_clause,[],[f281,f326,f257])).

fof(f281,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k2_tarski(sK0,sK2))
    | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( k1_tarski(sK0) != X0
      | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),k2_tarski(sK0,sK2))
      | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),X0) ) ),
    inference(superposition,[],[f29,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1108,plain,(
    ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f1107])).

fof(f1107,plain,
    ( $false
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f1106,f54])).

fof(f1106,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK2))
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f1105,f27])).

fof(f1105,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK2))
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f1104,f29])).

fof(f1104,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK2))
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f1088,f57])).

fof(f1088,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK2))
    | ~ spl6_13 ),
    inference(superposition,[],[f35,f580])).

fof(f580,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0))
    | ~ spl6_13 ),
    inference(resolution,[],[f259,f58])).

fof(f58,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f259,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f257])).

fof(f67,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f28,f64,f60])).

fof(f28,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (3157)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (3171)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (3147)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (3148)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (3156)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (3145)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (3163)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (3146)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (3153)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (3149)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (3173)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (3169)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (3167)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (3170)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (3160)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (3159)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (3174)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (3154)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (3165)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (3159)Refutation not found, incomplete strategy% (3159)------------------------------
% 0.21/0.53  % (3159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3159)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3159)Memory used [KB]: 1663
% 0.21/0.53  % (3159)Time elapsed: 0.091 s
% 0.21/0.53  % (3159)------------------------------
% 0.21/0.53  % (3159)------------------------------
% 0.21/0.53  % (3164)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (3150)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (3151)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (3161)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (3166)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (3172)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (3168)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (3155)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (3155)Refutation not found, incomplete strategy% (3155)------------------------------
% 0.21/0.54  % (3155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3155)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3155)Memory used [KB]: 10746
% 0.21/0.54  % (3155)Time elapsed: 0.139 s
% 0.21/0.54  % (3155)------------------------------
% 0.21/0.54  % (3155)------------------------------
% 0.21/0.55  % (3173)Refutation not found, incomplete strategy% (3173)------------------------------
% 0.21/0.55  % (3173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3173)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3173)Memory used [KB]: 10746
% 0.21/0.55  % (3173)Time elapsed: 0.130 s
% 0.21/0.55  % (3173)------------------------------
% 0.21/0.55  % (3173)------------------------------
% 0.21/0.55  % (3158)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (3152)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (3162)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (3161)Refutation not found, incomplete strategy% (3161)------------------------------
% 0.21/0.55  % (3161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3161)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3161)Memory used [KB]: 10618
% 0.21/0.55  % (3161)Time elapsed: 0.151 s
% 0.21/0.55  % (3161)------------------------------
% 0.21/0.55  % (3161)------------------------------
% 0.21/0.55  % (3162)Refutation not found, incomplete strategy% (3162)------------------------------
% 0.21/0.55  % (3162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3162)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3162)Memory used [KB]: 1663
% 0.21/0.55  % (3162)Time elapsed: 0.160 s
% 0.21/0.55  % (3162)------------------------------
% 0.21/0.55  % (3162)------------------------------
% 2.09/0.63  % (3157)Refutation found. Thanks to Tanya!
% 2.09/0.63  % SZS status Theorem for theBenchmark
% 2.21/0.65  % SZS output start Proof for theBenchmark
% 2.21/0.65  fof(f1372,plain,(
% 2.21/0.65    $false),
% 2.21/0.65    inference(avatar_sat_refutation,[],[f67,f1108,f1110,f1209,f1295,f1346,f1348])).
% 2.21/0.65  fof(f1348,plain,(
% 2.21/0.65    ~spl6_2 | spl6_27 | ~spl6_28),
% 2.21/0.65    inference(avatar_split_clause,[],[f1319,f1206,f1202,f64])).
% 2.21/0.65  fof(f64,plain,(
% 2.21/0.65    spl6_2 <=> sK0 = sK2),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.21/0.65  fof(f1202,plain,(
% 2.21/0.65    spl6_27 <=> sK0 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.21/0.65  fof(f1206,plain,(
% 2.21/0.65    spl6_28 <=> sK2 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.21/0.65  fof(f1319,plain,(
% 2.21/0.65    sK0 != sK2 | (spl6_27 | ~spl6_28)),
% 2.21/0.65    inference(superposition,[],[f1203,f1208])).
% 2.21/0.65  fof(f1208,plain,(
% 2.21/0.65    sK2 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)) | ~spl6_28),
% 2.21/0.65    inference(avatar_component_clause,[],[f1206])).
% 2.21/0.65  fof(f1203,plain,(
% 2.21/0.65    sK0 != sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)) | spl6_27),
% 2.21/0.65    inference(avatar_component_clause,[],[f1202])).
% 2.21/0.65  fof(f1346,plain,(
% 2.21/0.65    spl6_1 | spl6_13 | ~spl6_28),
% 2.21/0.65    inference(avatar_split_clause,[],[f1345,f1206,f257,f60])).
% 2.21/0.65  fof(f60,plain,(
% 2.21/0.65    spl6_1 <=> r2_hidden(sK2,sK1)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.21/0.65  fof(f257,plain,(
% 2.21/0.65    spl6_13 <=> r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.21/0.65  fof(f1345,plain,(
% 2.21/0.65    r2_hidden(sK2,sK1) | (spl6_13 | ~spl6_28)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1344,f1321])).
% 2.21/0.65  fof(f1321,plain,(
% 2.21/0.65    ~r2_hidden(sK2,k1_tarski(sK0)) | (spl6_13 | ~spl6_28)),
% 2.21/0.65    inference(superposition,[],[f258,f1208])).
% 2.21/0.65  fof(f258,plain,(
% 2.21/0.65    ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl6_13),
% 2.21/0.65    inference(avatar_component_clause,[],[f257])).
% 2.21/0.65  fof(f1344,plain,(
% 2.21/0.65    r2_hidden(sK2,sK1) | r2_hidden(sK2,k1_tarski(sK0)) | ~spl6_28),
% 2.21/0.65    inference(subsumption_resolution,[],[f1325,f29])).
% 2.21/0.65  fof(f29,plain,(
% 2.21/0.65    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 2.21/0.65    inference(cnf_transformation,[],[f12])).
% 2.21/0.65  fof(f12,plain,(
% 2.21/0.65    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & (sK0 = sK2 | ~r2_hidden(sK2,sK1)) & r2_hidden(sK0,sK1)),
% 2.21/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 2.21/0.65  fof(f11,plain,(
% 2.21/0.65    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & (sK0 = sK2 | ~r2_hidden(sK2,sK1)) & r2_hidden(sK0,sK1))),
% 2.21/0.65    introduced(choice_axiom,[])).
% 2.21/0.65  fof(f10,plain,(
% 2.21/0.65    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 2.21/0.65    inference(flattening,[],[f9])).
% 2.21/0.65  fof(f9,plain,(
% 2.21/0.65    ? [X0,X1,X2] : ((k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 2.21/0.65    inference(ennf_transformation,[],[f8])).
% 2.21/0.65  fof(f8,negated_conjecture,(
% 2.21/0.65    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 2.21/0.65    inference(negated_conjecture,[],[f7])).
% 2.21/0.65  fof(f7,conjecture,(
% 2.21/0.65    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 2.21/0.65  fof(f1325,plain,(
% 2.21/0.65    r2_hidden(sK2,sK1) | k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK2),sK1) | r2_hidden(sK2,k1_tarski(sK0)) | ~spl6_28),
% 2.21/0.65    inference(superposition,[],[f34,f1208])).
% 2.21/0.65  fof(f34,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f17])).
% 2.21/0.65  fof(f17,plain,(
% 2.21/0.65    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.21/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 2.21/0.65  fof(f16,plain,(
% 2.21/0.65    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.21/0.65    introduced(choice_axiom,[])).
% 2.21/0.65  fof(f15,plain,(
% 2.21/0.65    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.21/0.65    inference(rectify,[],[f14])).
% 2.21/0.65  fof(f14,plain,(
% 2.21/0.65    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.21/0.65    inference(flattening,[],[f13])).
% 2.21/0.65  fof(f13,plain,(
% 2.21/0.65    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.21/0.65    inference(nnf_transformation,[],[f2])).
% 2.21/0.65  fof(f2,axiom,(
% 2.21/0.65    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.21/0.65  fof(f1295,plain,(
% 2.21/0.65    ~spl6_27),
% 2.21/0.65    inference(avatar_contradiction_clause,[],[f1294])).
% 2.21/0.65  fof(f1294,plain,(
% 2.21/0.65    $false | ~spl6_27),
% 2.21/0.65    inference(subsumption_resolution,[],[f1293,f54])).
% 2.21/0.65  fof(f54,plain,(
% 2.21/0.65    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 2.21/0.65    inference(equality_resolution,[],[f53])).
% 2.21/0.65  fof(f53,plain,(
% 2.21/0.65    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 2.21/0.65    inference(equality_resolution,[],[f38])).
% 2.21/0.65  fof(f38,plain,(
% 2.21/0.65    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f22,plain,(
% 2.21/0.65    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.21/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 2.21/0.65  fof(f21,plain,(
% 2.21/0.65    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.21/0.65    introduced(choice_axiom,[])).
% 2.21/0.65  fof(f20,plain,(
% 2.21/0.65    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.21/0.65    inference(rectify,[],[f19])).
% 2.21/0.65  fof(f19,plain,(
% 2.21/0.65    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.21/0.65    inference(flattening,[],[f18])).
% 2.21/0.65  fof(f18,plain,(
% 2.21/0.65    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.21/0.65    inference(nnf_transformation,[],[f4])).
% 2.21/0.65  fof(f4,axiom,(
% 2.21/0.65    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.21/0.65  fof(f1293,plain,(
% 2.21/0.65    ~r2_hidden(sK0,k2_tarski(sK0,sK2)) | ~spl6_27),
% 2.21/0.65    inference(subsumption_resolution,[],[f1292,f27])).
% 2.21/0.65  fof(f27,plain,(
% 2.21/0.65    r2_hidden(sK0,sK1)),
% 2.21/0.65    inference(cnf_transformation,[],[f12])).
% 2.21/0.65  fof(f1292,plain,(
% 2.21/0.65    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k2_tarski(sK0,sK2)) | ~spl6_27),
% 2.21/0.65    inference(subsumption_resolution,[],[f1291,f29])).
% 2.21/0.65  fof(f1291,plain,(
% 2.21/0.65    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK2),sK1) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k2_tarski(sK0,sK2)) | ~spl6_27),
% 2.21/0.65    inference(subsumption_resolution,[],[f1275,f57])).
% 2.21/0.65  fof(f57,plain,(
% 2.21/0.65    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.21/0.65    inference(equality_resolution,[],[f56])).
% 2.21/0.65  fof(f56,plain,(
% 2.21/0.65    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.21/0.65    inference(equality_resolution,[],[f44])).
% 2.21/0.65  fof(f44,plain,(
% 2.21/0.65    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.21/0.65    inference(cnf_transformation,[],[f26])).
% 2.21/0.65  fof(f26,plain,(
% 2.21/0.65    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.21/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 2.21/0.65  fof(f25,plain,(
% 2.21/0.65    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 2.21/0.65    introduced(choice_axiom,[])).
% 2.21/0.65  fof(f24,plain,(
% 2.21/0.65    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.21/0.65    inference(rectify,[],[f23])).
% 2.21/0.65  fof(f23,plain,(
% 2.21/0.65    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.21/0.65    inference(nnf_transformation,[],[f3])).
% 2.21/0.65  fof(f3,axiom,(
% 2.21/0.65    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.21/0.65  fof(f1275,plain,(
% 2.21/0.65    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK2),sK1) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k2_tarski(sK0,sK2)) | ~spl6_27),
% 2.21/0.65    inference(superposition,[],[f35,f1204])).
% 2.21/0.65  fof(f1204,plain,(
% 2.21/0.65    sK0 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)) | ~spl6_27),
% 2.21/0.65    inference(avatar_component_clause,[],[f1202])).
% 2.21/0.65  fof(f35,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f17])).
% 2.21/0.65  fof(f1209,plain,(
% 2.21/0.65    spl6_27 | spl6_28 | ~spl6_15),
% 2.21/0.65    inference(avatar_split_clause,[],[f1193,f326,f1206,f1202])).
% 2.21/0.65  fof(f326,plain,(
% 2.21/0.65    spl6_15 <=> r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k2_tarski(sK0,sK2))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.21/0.65  fof(f1193,plain,(
% 2.21/0.65    sK2 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)) | sK0 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)) | ~spl6_15),
% 2.21/0.65    inference(resolution,[],[f327,f55])).
% 2.21/0.65  fof(f55,plain,(
% 2.21/0.65    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 2.21/0.65    inference(equality_resolution,[],[f37])).
% 2.21/0.65  fof(f37,plain,(
% 2.21/0.65    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f327,plain,(
% 2.21/0.65    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k2_tarski(sK0,sK2)) | ~spl6_15),
% 2.21/0.65    inference(avatar_component_clause,[],[f326])).
% 2.21/0.65  fof(f1110,plain,(
% 2.21/0.65    spl6_13 | spl6_15),
% 2.21/0.65    inference(avatar_split_clause,[],[f281,f326,f257])).
% 2.21/0.65  fof(f281,plain,(
% 2.21/0.65    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k2_tarski(sK0,sK2)) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.21/0.65    inference(equality_resolution,[],[f86])).
% 2.21/0.65  fof(f86,plain,(
% 2.21/0.65    ( ! [X0] : (k1_tarski(sK0) != X0 | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),k2_tarski(sK0,sK2)) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),X0)) )),
% 2.21/0.65    inference(superposition,[],[f29,f33])).
% 2.21/0.65  fof(f33,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f17])).
% 2.21/0.65  fof(f1108,plain,(
% 2.21/0.65    ~spl6_13),
% 2.21/0.65    inference(avatar_contradiction_clause,[],[f1107])).
% 2.21/0.65  fof(f1107,plain,(
% 2.21/0.65    $false | ~spl6_13),
% 2.21/0.65    inference(subsumption_resolution,[],[f1106,f54])).
% 2.21/0.65  fof(f1106,plain,(
% 2.21/0.65    ~r2_hidden(sK0,k2_tarski(sK0,sK2)) | ~spl6_13),
% 2.21/0.65    inference(subsumption_resolution,[],[f1105,f27])).
% 2.21/0.65  fof(f1105,plain,(
% 2.21/0.65    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k2_tarski(sK0,sK2)) | ~spl6_13),
% 2.21/0.65    inference(subsumption_resolution,[],[f1104,f29])).
% 2.21/0.65  fof(f1104,plain,(
% 2.21/0.65    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK2),sK1) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k2_tarski(sK0,sK2)) | ~spl6_13),
% 2.21/0.65    inference(subsumption_resolution,[],[f1088,f57])).
% 2.21/0.65  fof(f1088,plain,(
% 2.21/0.65    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK2),sK1) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k2_tarski(sK0,sK2)) | ~spl6_13),
% 2.21/0.65    inference(superposition,[],[f35,f580])).
% 2.21/0.65  fof(f580,plain,(
% 2.21/0.65    sK0 = sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)) | ~spl6_13),
% 2.21/0.65    inference(resolution,[],[f259,f58])).
% 2.21/0.65  fof(f58,plain,(
% 2.21/0.65    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.21/0.65    inference(equality_resolution,[],[f43])).
% 2.21/0.65  fof(f43,plain,(
% 2.21/0.65    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.21/0.65    inference(cnf_transformation,[],[f26])).
% 2.21/0.65  fof(f259,plain,(
% 2.21/0.65    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl6_13),
% 2.21/0.65    inference(avatar_component_clause,[],[f257])).
% 2.21/0.65  fof(f67,plain,(
% 2.21/0.65    ~spl6_1 | spl6_2),
% 2.21/0.65    inference(avatar_split_clause,[],[f28,f64,f60])).
% 2.21/0.65  fof(f28,plain,(
% 2.21/0.65    sK0 = sK2 | ~r2_hidden(sK2,sK1)),
% 2.21/0.65    inference(cnf_transformation,[],[f12])).
% 2.21/0.65  % SZS output end Proof for theBenchmark
% 2.21/0.65  % (3157)------------------------------
% 2.21/0.65  % (3157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (3157)Termination reason: Refutation
% 2.21/0.65  
% 2.21/0.65  % (3157)Memory used [KB]: 11513
% 2.21/0.65  % (3157)Time elapsed: 0.230 s
% 2.21/0.65  % (3157)------------------------------
% 2.21/0.65  % (3157)------------------------------
% 2.21/0.66  % (3144)Success in time 0.293 s
%------------------------------------------------------------------------------
