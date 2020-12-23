%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:13 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 118 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  301 ( 589 expanded)
%              Number of equality atoms :   73 ( 166 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f155,f164,f482,f1206])).

fof(f1206,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f1205])).

fof(f1205,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f1204,f231])).

fof(f231,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl6_1
    | spl6_2 ),
    inference(superposition,[],[f143,f180])).

fof(f180,plain,
    ( sK0 = sK2(k1_tarski(sK0),sK1,k1_tarski(sK0))
    | ~ spl6_1 ),
    inference(resolution,[],[f140,f70])).

fof(f70,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f140,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl6_1
  <=> r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f143,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl6_2
  <=> r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1204,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f1203,f79])).

fof(f79,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f37,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f37,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f1203,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,sK1)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f1187,f69])).

fof(f69,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1187,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,sK1)
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f1186])).

fof(f1186,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl6_3 ),
    inference(superposition,[],[f57,f1107])).

fof(f1107,plain,
    ( sK0 = sK4(k1_tarski(sK0),sK1,k1_tarski(sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f403,f70])).

fof(f403,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f401])).

fof(f401,plain,
    ( spl6_3
  <=> r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f482,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f480,f401])).

fof(f480,plain,(
    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f479])).

fof(f479,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( k1_tarski(sK0) != X0
      | r2_hidden(sK4(k1_tarski(sK0),sK1,X0),k1_tarski(sK0))
      | r2_hidden(sK4(k1_tarski(sK0),sK1,X0),X0) ) ),
    inference(superposition,[],[f79,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f164,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f160,f138])).

fof(f160,plain,(
    r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( k1_tarski(sK0) != X0
      | r2_hidden(sK2(k1_tarski(sK0),sK1,X0),k1_tarski(sK0))
      | r2_hidden(sK2(k1_tarski(sK0),sK1,X0),X0) ) ),
    inference(superposition,[],[f38,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f38,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f155,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f154,f142,f138])).

fof(f154,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f153,f38])).

fof(f153,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f144,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f144,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:34:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (29402)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (29417)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.51  % (29408)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.51  % (29401)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (29399)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (29412)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (29400)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (29410)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (29399)Refutation not found, incomplete strategy% (29399)------------------------------
% 0.22/0.53  % (29399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (29399)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (29399)Memory used [KB]: 1663
% 0.22/0.53  % (29399)Time elapsed: 0.126 s
% 0.22/0.53  % (29399)------------------------------
% 0.22/0.53  % (29399)------------------------------
% 0.22/0.54  % (29403)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (29412)Refutation not found, incomplete strategy% (29412)------------------------------
% 0.22/0.54  % (29412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29412)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (29412)Memory used [KB]: 1663
% 0.22/0.54  % (29412)Time elapsed: 0.129 s
% 0.22/0.54  % (29412)------------------------------
% 0.22/0.54  % (29412)------------------------------
% 0.22/0.54  % (29422)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (29424)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (29422)Refutation not found, incomplete strategy% (29422)------------------------------
% 0.22/0.54  % (29422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29426)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (29418)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (29416)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (29423)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (29425)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (29427)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (29409)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (29398)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (29405)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (29411)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (29407)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (29425)Refutation not found, incomplete strategy% (29425)------------------------------
% 0.22/0.55  % (29425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29425)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (29425)Memory used [KB]: 6140
% 0.22/0.55  % (29425)Time elapsed: 0.152 s
% 0.22/0.55  % (29425)------------------------------
% 0.22/0.55  % (29425)------------------------------
% 0.22/0.55  % (29419)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (29416)Refutation not found, incomplete strategy% (29416)------------------------------
% 0.22/0.56  % (29416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (29416)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (29416)Memory used [KB]: 1663
% 0.22/0.56  % (29416)Time elapsed: 0.149 s
% 0.22/0.56  % (29416)------------------------------
% 0.22/0.56  % (29416)------------------------------
% 0.22/0.56  % (29421)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (29415)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (29420)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (29424)Refutation not found, incomplete strategy% (29424)------------------------------
% 0.22/0.56  % (29424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (29424)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (29424)Memory used [KB]: 6268
% 0.22/0.56  % (29424)Time elapsed: 0.148 s
% 0.22/0.56  % (29424)------------------------------
% 0.22/0.56  % (29424)------------------------------
% 0.22/0.56  % (29413)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (29406)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (29422)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (29422)Memory used [KB]: 10618
% 0.22/0.56  % (29422)Time elapsed: 0.130 s
% 0.22/0.56  % (29422)------------------------------
% 0.22/0.56  % (29422)------------------------------
% 0.22/0.57  % (29415)Refutation not found, incomplete strategy% (29415)------------------------------
% 0.22/0.57  % (29415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (29415)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (29415)Memory used [KB]: 1663
% 0.22/0.57  % (29415)Time elapsed: 0.160 s
% 0.22/0.57  % (29415)------------------------------
% 0.22/0.57  % (29415)------------------------------
% 0.22/0.57  % (29404)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.58  % (29414)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.75/0.59  % (29414)Refutation not found, incomplete strategy% (29414)------------------------------
% 1.75/0.59  % (29414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.59  % (29414)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.59  
% 1.75/0.59  % (29414)Memory used [KB]: 10618
% 1.75/0.59  % (29414)Time elapsed: 0.169 s
% 1.75/0.59  % (29414)------------------------------
% 1.75/0.59  % (29414)------------------------------
% 2.15/0.68  % (29450)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.15/0.68  % (29401)Refutation not found, incomplete strategy% (29401)------------------------------
% 2.15/0.68  % (29401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.68  % (29401)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.68  
% 2.15/0.68  % (29401)Memory used [KB]: 6140
% 2.15/0.68  % (29401)Time elapsed: 0.269 s
% 2.15/0.68  % (29401)------------------------------
% 2.15/0.68  % (29401)------------------------------
% 2.15/0.68  % (29452)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.15/0.68  % (29451)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.15/0.68  % (29455)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.15/0.69  % (29410)Refutation found. Thanks to Tanya!
% 2.15/0.69  % SZS status Theorem for theBenchmark
% 2.15/0.69  % SZS output start Proof for theBenchmark
% 2.15/0.69  fof(f1207,plain,(
% 2.15/0.69    $false),
% 2.15/0.69    inference(avatar_sat_refutation,[],[f155,f164,f482,f1206])).
% 2.15/0.69  fof(f1206,plain,(
% 2.15/0.69    ~spl6_1 | spl6_2 | ~spl6_3),
% 2.15/0.69    inference(avatar_contradiction_clause,[],[f1205])).
% 2.15/0.69  fof(f1205,plain,(
% 2.15/0.69    $false | (~spl6_1 | spl6_2 | ~spl6_3)),
% 2.15/0.69    inference(subsumption_resolution,[],[f1204,f231])).
% 2.15/0.69  fof(f231,plain,(
% 2.15/0.69    ~r2_hidden(sK0,sK1) | (~spl6_1 | spl6_2)),
% 2.15/0.69    inference(superposition,[],[f143,f180])).
% 2.15/0.69  fof(f180,plain,(
% 2.15/0.69    sK0 = sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)) | ~spl6_1),
% 2.15/0.69    inference(resolution,[],[f140,f70])).
% 2.15/0.69  fof(f70,plain,(
% 2.15/0.69    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.15/0.69    inference(equality_resolution,[],[f47])).
% 2.15/0.69  fof(f47,plain,(
% 2.15/0.69    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.15/0.69    inference(cnf_transformation,[],[f26])).
% 2.15/0.69  fof(f26,plain,(
% 2.15/0.69    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.15/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 2.15/0.69  fof(f25,plain,(
% 2.15/0.69    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 2.15/0.69    introduced(choice_axiom,[])).
% 2.15/0.69  fof(f24,plain,(
% 2.15/0.69    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.15/0.69    inference(rectify,[],[f23])).
% 2.15/0.69  fof(f23,plain,(
% 2.15/0.69    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.15/0.69    inference(nnf_transformation,[],[f6])).
% 2.15/0.69  fof(f6,axiom,(
% 2.15/0.69    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.15/0.69  fof(f140,plain,(
% 2.15/0.69    r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl6_1),
% 2.15/0.69    inference(avatar_component_clause,[],[f138])).
% 2.15/0.69  fof(f138,plain,(
% 2.15/0.69    spl6_1 <=> r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.15/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.15/0.69  fof(f143,plain,(
% 2.15/0.69    ~r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1) | spl6_2),
% 2.15/0.69    inference(avatar_component_clause,[],[f142])).
% 2.15/0.69  fof(f142,plain,(
% 2.15/0.69    spl6_2 <=> r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1)),
% 2.15/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.15/0.69  fof(f1204,plain,(
% 2.15/0.69    r2_hidden(sK0,sK1) | ~spl6_3),
% 2.15/0.69    inference(subsumption_resolution,[],[f1203,f79])).
% 2.15/0.69  fof(f79,plain,(
% 2.15/0.69    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 2.15/0.69    inference(resolution,[],[f37,f46])).
% 2.15/0.69  fof(f46,plain,(
% 2.15/0.69    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.15/0.69    inference(cnf_transformation,[],[f15])).
% 2.15/0.69  fof(f15,plain,(
% 2.15/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 2.15/0.69    inference(ennf_transformation,[],[f13])).
% 2.15/0.69  fof(f13,plain,(
% 2.15/0.69    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 2.15/0.69    inference(unused_predicate_definition_removal,[],[f5])).
% 2.15/0.69  fof(f5,axiom,(
% 2.15/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.15/0.69  fof(f37,plain,(
% 2.15/0.69    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 2.15/0.69    inference(cnf_transformation,[],[f17])).
% 2.15/0.69  fof(f17,plain,(
% 2.15/0.69    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 2.15/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 2.15/0.69  fof(f16,plain,(
% 2.15/0.69    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 2.15/0.69    introduced(choice_axiom,[])).
% 2.15/0.69  fof(f14,plain,(
% 2.15/0.69    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.15/0.69    inference(ennf_transformation,[],[f12])).
% 2.15/0.69  fof(f12,negated_conjecture,(
% 2.15/0.69    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.15/0.69    inference(negated_conjecture,[],[f11])).
% 2.15/0.69  fof(f11,conjecture,(
% 2.15/0.69    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 2.15/0.69  fof(f1203,plain,(
% 2.15/0.69    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,sK1) | ~spl6_3),
% 2.15/0.69    inference(subsumption_resolution,[],[f1187,f69])).
% 2.15/0.69  fof(f69,plain,(
% 2.15/0.69    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.15/0.69    inference(equality_resolution,[],[f68])).
% 2.15/0.69  fof(f68,plain,(
% 2.15/0.69    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.15/0.69    inference(equality_resolution,[],[f48])).
% 2.15/0.69  fof(f48,plain,(
% 2.15/0.69    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.15/0.69    inference(cnf_transformation,[],[f26])).
% 2.15/0.69  fof(f1187,plain,(
% 2.15/0.69    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,sK1) | ~spl6_3),
% 2.15/0.69    inference(duplicate_literal_removal,[],[f1186])).
% 2.15/0.69  fof(f1186,plain,(
% 2.15/0.69    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k1_tarski(sK0)) | ~spl6_3),
% 2.15/0.69    inference(superposition,[],[f57,f1107])).
% 2.15/0.69  fof(f1107,plain,(
% 2.15/0.69    sK0 = sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)) | ~spl6_3),
% 2.15/0.69    inference(resolution,[],[f403,f70])).
% 2.15/0.69  fof(f403,plain,(
% 2.15/0.69    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl6_3),
% 2.15/0.69    inference(avatar_component_clause,[],[f401])).
% 2.15/0.69  fof(f401,plain,(
% 2.15/0.69    spl6_3 <=> r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.15/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.15/0.69  fof(f57,plain,(
% 2.15/0.69    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.15/0.69    inference(cnf_transformation,[],[f31])).
% 2.15/0.69  fof(f31,plain,(
% 2.15/0.69    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.15/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 2.15/0.69  fof(f30,plain,(
% 2.15/0.69    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.15/0.69    introduced(choice_axiom,[])).
% 2.15/0.69  fof(f29,plain,(
% 2.15/0.69    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.15/0.69    inference(rectify,[],[f28])).
% 2.15/0.69  fof(f28,plain,(
% 2.15/0.69    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.15/0.69    inference(flattening,[],[f27])).
% 2.15/0.69  fof(f27,plain,(
% 2.15/0.69    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.15/0.69    inference(nnf_transformation,[],[f3])).
% 2.15/0.69  fof(f3,axiom,(
% 2.15/0.69    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.15/0.69  fof(f482,plain,(
% 2.15/0.69    spl6_3),
% 2.15/0.69    inference(avatar_split_clause,[],[f480,f401])).
% 2.15/0.69  fof(f480,plain,(
% 2.15/0.69    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.15/0.69    inference(duplicate_literal_removal,[],[f479])).
% 2.15/0.69  fof(f479,plain,(
% 2.15/0.69    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.15/0.69    inference(equality_resolution,[],[f93])).
% 2.15/0.69  fof(f93,plain,(
% 2.15/0.69    ( ! [X0] : (k1_tarski(sK0) != X0 | r2_hidden(sK4(k1_tarski(sK0),sK1,X0),k1_tarski(sK0)) | r2_hidden(sK4(k1_tarski(sK0),sK1,X0),X0)) )),
% 2.15/0.69    inference(superposition,[],[f79,f55])).
% 2.15/0.69  fof(f55,plain,(
% 2.15/0.69    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.15/0.69    inference(cnf_transformation,[],[f31])).
% 2.15/0.69  fof(f164,plain,(
% 2.15/0.69    spl6_1),
% 2.15/0.69    inference(avatar_split_clause,[],[f160,f138])).
% 2.15/0.69  fof(f160,plain,(
% 2.15/0.69    r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.15/0.69    inference(duplicate_literal_removal,[],[f159])).
% 2.15/0.69  fof(f159,plain,(
% 2.15/0.69    r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.15/0.69    inference(equality_resolution,[],[f87])).
% 2.15/0.69  fof(f87,plain,(
% 2.15/0.69    ( ! [X0] : (k1_tarski(sK0) != X0 | r2_hidden(sK2(k1_tarski(sK0),sK1,X0),k1_tarski(sK0)) | r2_hidden(sK2(k1_tarski(sK0),sK1,X0),X0)) )),
% 2.15/0.69    inference(superposition,[],[f38,f42])).
% 2.15/0.69  fof(f42,plain,(
% 2.15/0.69    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.15/0.69    inference(cnf_transformation,[],[f22])).
% 2.15/0.69  fof(f22,plain,(
% 2.15/0.69    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.15/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 2.15/0.69  fof(f21,plain,(
% 2.15/0.69    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.15/0.69    introduced(choice_axiom,[])).
% 2.15/0.69  fof(f20,plain,(
% 2.15/0.69    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.15/0.69    inference(rectify,[],[f19])).
% 2.15/0.69  fof(f19,plain,(
% 2.15/0.69    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.15/0.69    inference(flattening,[],[f18])).
% 2.15/0.69  fof(f18,plain,(
% 2.15/0.69    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.15/0.69    inference(nnf_transformation,[],[f2])).
% 2.15/0.69  fof(f2,axiom,(
% 2.15/0.69    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.15/0.69  fof(f38,plain,(
% 2.15/0.69    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 2.15/0.69    inference(cnf_transformation,[],[f17])).
% 2.15/0.69  fof(f155,plain,(
% 2.15/0.69    ~spl6_1 | ~spl6_2),
% 2.15/0.69    inference(avatar_split_clause,[],[f154,f142,f138])).
% 2.15/0.69  fof(f154,plain,(
% 2.15/0.69    ~r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl6_2),
% 2.15/0.69    inference(subsumption_resolution,[],[f153,f38])).
% 2.15/0.69  fof(f153,plain,(
% 2.15/0.69    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl6_2),
% 2.15/0.69    inference(duplicate_literal_removal,[],[f146])).
% 2.15/0.69  fof(f146,plain,(
% 2.15/0.69    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl6_2),
% 2.15/0.69    inference(resolution,[],[f144,f44])).
% 2.15/0.69  fof(f44,plain,(
% 2.15/0.69    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.15/0.69    inference(cnf_transformation,[],[f22])).
% 2.15/0.69  fof(f144,plain,(
% 2.15/0.69    r2_hidden(sK2(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1) | ~spl6_2),
% 2.15/0.69    inference(avatar_component_clause,[],[f142])).
% 2.15/0.69  % SZS output end Proof for theBenchmark
% 2.15/0.69  % (29410)------------------------------
% 2.15/0.69  % (29410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.69  % (29410)Termination reason: Refutation
% 2.15/0.69  
% 2.15/0.69  % (29410)Memory used [KB]: 11513
% 2.15/0.69  % (29410)Time elapsed: 0.266 s
% 2.15/0.69  % (29410)------------------------------
% 2.15/0.69  % (29410)------------------------------
% 2.15/0.69  % (29397)Success in time 0.322 s
%------------------------------------------------------------------------------
