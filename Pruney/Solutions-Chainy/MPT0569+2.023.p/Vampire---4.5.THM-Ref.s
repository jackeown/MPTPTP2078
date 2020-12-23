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
% DateTime   : Thu Dec  3 12:50:29 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 239 expanded)
%              Number of leaves         :   30 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  355 ( 748 expanded)
%              Number of equality atoms :   60 ( 129 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1484,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f115,f120,f141,f253,f300,f480,f619,f641,f642,f728,f786,f1412,f1483])).

fof(f1483,plain,(
    spl9_6 ),
    inference(avatar_contradiction_clause,[],[f1482])).

fof(f1482,plain,
    ( $false
    | spl9_6 ),
    inference(subsumption_resolution,[],[f1473,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f1473,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0)
    | spl9_6 ),
    inference(resolution,[],[f157,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f157,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl9_6
  <=> r1_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f1412,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_52 ),
    inference(avatar_contradiction_clause,[],[f1411])).

fof(f1411,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_52 ),
    inference(subsumption_resolution,[],[f1410,f187])).

fof(f187,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f179,f68])).

fof(f179,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0)))
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f158,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f77,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f158,plain,
    ( r1_xboole_0(k1_xboole_0,sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f1410,plain,
    ( r2_hidden(sK7(sK1,sK3(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f1365,f108])).

fof(f108,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl9_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f1365,plain,
    ( r2_hidden(sK7(sK1,sK3(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0))
    | ~ spl9_3
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_52 ),
    inference(unit_resulting_resolution,[],[f119,f219,f224,f785,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
            & r2_hidden(sK8(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
        & r2_hidden(sK8(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f785,plain,
    ( r2_hidden(k4_tarski(sK7(sK1,sK3(k2_relat_1(sK1),sK0)),sK3(k2_relat_1(sK1),sK0)),sK1)
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f783])).

fof(f783,plain,
    ( spl9_52
  <=> r2_hidden(k4_tarski(sK7(sK1,sK3(k2_relat_1(sK1),sK0)),sK3(k2_relat_1(sK1),sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f224,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl9_13
  <=> r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f219,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1),sK0),sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl9_12
  <=> r2_hidden(sK3(k2_relat_1(sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f119,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl9_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f786,plain,
    ( spl9_52
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f753,f222,f783])).

fof(f753,plain,
    ( r2_hidden(k4_tarski(sK7(sK1,sK3(k2_relat_1(sK1),sK0)),sK3(k2_relat_1(sK1),sK0)),sK1)
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f224,f105])).

fof(f105,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f54,f57,f56,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f728,plain,
    ( k2_relat_1(k1_xboole_0) != k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k10_relat_1(sK1,sK0) != k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))
    | k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f642,plain,
    ( spl9_13
    | spl9_2 ),
    inference(avatar_split_clause,[],[f630,f111,f222])).

fof(f111,plain,
    ( spl9_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f630,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f113,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f113,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f641,plain,
    ( spl9_12
    | spl9_2 ),
    inference(avatar_split_clause,[],[f631,f111,f217])).

fof(f631,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1),sK0),sK0)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f113,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f619,plain,
    ( spl9_39
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f608,f161,f117,f616])).

fof(f616,plain,
    ( spl9_39
  <=> k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f161,plain,
    ( spl9_7
  <=> k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f608,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(superposition,[],[f123,f163])).

fof(f163,plain,
    ( k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f123,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0)))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f119,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f81,f75])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f480,plain,
    ( spl9_25
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f454,f161,f156,f111,f477])).

fof(f477,plain,
    ( spl9_25
  <=> k2_relat_1(k1_xboole_0) = k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f454,plain,
    ( k2_relat_1(k1_xboole_0) = k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f187,f444,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f444,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl9_2
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f145,f163])).

fof(f145,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),sK0)))
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f112,f100])).

fof(f112,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f300,plain,
    ( spl9_14
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f277,f156,f296])).

fof(f296,plain,
    ( spl9_14
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f277,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f187,f187,f90])).

fof(f253,plain,
    ( spl9_7
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f242,f111,f161])).

fof(f242,plain,
    ( k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl9_2 ),
    inference(resolution,[],[f112,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f141,plain,
    ( spl9_5
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f124,f117,f137])).

fof(f137,plain,
    ( spl9_5
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f124,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl9_3 ),
    inference(resolution,[],[f119,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(f120,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f63,f117])).

fof(f63,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f42])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f115,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f64,f111,f107])).

fof(f64,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f114,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f65,f111,f107])).

fof(f65,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (30639)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (30644)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (30644)Refutation not found, incomplete strategy% (30644)------------------------------
% 0.21/0.51  % (30644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30633)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (30637)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (30641)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (30658)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.53  % (30644)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (30644)Memory used [KB]: 10618
% 1.31/0.53  % (30644)Time elapsed: 0.104 s
% 1.31/0.53  % (30644)------------------------------
% 1.31/0.53  % (30644)------------------------------
% 1.31/0.53  % (30647)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.53  % (30641)Refutation not found, incomplete strategy% (30641)------------------------------
% 1.31/0.53  % (30641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (30641)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (30641)Memory used [KB]: 10618
% 1.31/0.53  % (30641)Time elapsed: 0.120 s
% 1.31/0.53  % (30641)------------------------------
% 1.31/0.53  % (30641)------------------------------
% 1.31/0.53  % (30656)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.53  % (30635)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.53  % (30648)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.53  % (30634)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.53  % (30632)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.53  % (30655)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.53  % (30632)Refutation not found, incomplete strategy% (30632)------------------------------
% 1.31/0.53  % (30632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (30632)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (30632)Memory used [KB]: 1663
% 1.31/0.53  % (30632)Time elapsed: 0.124 s
% 1.31/0.53  % (30632)------------------------------
% 1.31/0.53  % (30632)------------------------------
% 1.31/0.53  % (30645)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (30636)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.54  % (30650)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.54  % (30650)Refutation not found, incomplete strategy% (30650)------------------------------
% 1.31/0.54  % (30650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (30650)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (30650)Memory used [KB]: 10618
% 1.31/0.54  % (30650)Time elapsed: 0.131 s
% 1.31/0.54  % (30650)------------------------------
% 1.31/0.54  % (30650)------------------------------
% 1.31/0.54  % (30649)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.54  % (30662)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.54  % (30659)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.54  % (30657)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.50/0.54  % (30660)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.54  % (30661)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.55  % (30651)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.55  % (30652)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.55  % (30640)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.50/0.55  % (30642)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.55  % (30654)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.55  % (30638)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.55  % (30653)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.55  % (30646)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.50/0.55  % (30642)Refutation not found, incomplete strategy% (30642)------------------------------
% 1.50/0.55  % (30642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (30642)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (30642)Memory used [KB]: 10618
% 1.50/0.55  % (30642)Time elapsed: 0.149 s
% 1.50/0.55  % (30642)------------------------------
% 1.50/0.55  % (30642)------------------------------
% 1.50/0.56  % (30658)Refutation found. Thanks to Tanya!
% 1.50/0.56  % SZS status Theorem for theBenchmark
% 1.50/0.56  % SZS output start Proof for theBenchmark
% 1.50/0.56  fof(f1484,plain,(
% 1.50/0.56    $false),
% 1.50/0.56    inference(avatar_sat_refutation,[],[f114,f115,f120,f141,f253,f300,f480,f619,f641,f642,f728,f786,f1412,f1483])).
% 1.50/0.56  fof(f1483,plain,(
% 1.50/0.56    spl9_6),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f1482])).
% 1.50/0.56  fof(f1482,plain,(
% 1.50/0.56    $false | spl9_6),
% 1.50/0.56    inference(subsumption_resolution,[],[f1473,f68])).
% 1.50/0.56  fof(f68,plain,(
% 1.50/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f7])).
% 1.50/0.56  fof(f7,axiom,(
% 1.50/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.50/0.56  fof(f1473,plain,(
% 1.50/0.56    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0) | spl9_6),
% 1.50/0.56    inference(resolution,[],[f157,f87])).
% 1.50/0.56  fof(f87,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f52])).
% 1.50/0.56  fof(f52,plain,(
% 1.50/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.50/0.56    inference(nnf_transformation,[],[f11])).
% 1.50/0.56  fof(f11,axiom,(
% 1.50/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.50/0.56  fof(f157,plain,(
% 1.50/0.56    ~r1_xboole_0(k1_xboole_0,sK0) | spl9_6),
% 1.50/0.56    inference(avatar_component_clause,[],[f156])).
% 1.50/0.56  fof(f156,plain,(
% 1.50/0.56    spl9_6 <=> r1_xboole_0(k1_xboole_0,sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.50/0.56  fof(f1412,plain,(
% 1.50/0.56    ~spl9_1 | ~spl9_3 | ~spl9_6 | ~spl9_12 | ~spl9_13 | ~spl9_52),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f1411])).
% 1.50/0.56  fof(f1411,plain,(
% 1.50/0.56    $false | (~spl9_1 | ~spl9_3 | ~spl9_6 | ~spl9_12 | ~spl9_13 | ~spl9_52)),
% 1.50/0.56    inference(subsumption_resolution,[],[f1410,f187])).
% 1.50/0.56  fof(f187,plain,(
% 1.50/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl9_6),
% 1.50/0.56    inference(forward_demodulation,[],[f179,f68])).
% 1.50/0.56  fof(f179,plain,(
% 1.50/0.56    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0)))) ) | ~spl9_6),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f158,f100])).
% 1.50/0.56  fof(f100,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.50/0.56    inference(definition_unfolding,[],[f77,f75])).
% 1.50/0.56  fof(f75,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f6])).
% 1.50/0.56  fof(f6,axiom,(
% 1.50/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.50/0.56  fof(f77,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f45])).
% 1.50/0.56  fof(f45,plain,(
% 1.50/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.50/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f44])).
% 1.50/0.56  fof(f44,plain,(
% 1.50/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f29,plain,(
% 1.50/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.50/0.56    inference(ennf_transformation,[],[f24])).
% 1.50/0.56  fof(f24,plain,(
% 1.50/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.50/0.56    inference(rectify,[],[f3])).
% 1.50/0.56  fof(f3,axiom,(
% 1.50/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.50/0.56  fof(f158,plain,(
% 1.50/0.56    r1_xboole_0(k1_xboole_0,sK0) | ~spl9_6),
% 1.50/0.56    inference(avatar_component_clause,[],[f156])).
% 1.50/0.56  fof(f1410,plain,(
% 1.50/0.56    r2_hidden(sK7(sK1,sK3(k2_relat_1(sK1),sK0)),k1_xboole_0) | (~spl9_1 | ~spl9_3 | ~spl9_12 | ~spl9_13 | ~spl9_52)),
% 1.50/0.56    inference(forward_demodulation,[],[f1365,f108])).
% 1.50/0.56  fof(f108,plain,(
% 1.50/0.56    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl9_1),
% 1.50/0.56    inference(avatar_component_clause,[],[f107])).
% 1.50/0.56  fof(f107,plain,(
% 1.50/0.56    spl9_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.50/0.56  fof(f1365,plain,(
% 1.50/0.56    r2_hidden(sK7(sK1,sK3(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0)) | (~spl9_3 | ~spl9_12 | ~spl9_13 | ~spl9_52)),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f119,f219,f224,f785,f95])).
% 1.50/0.56  fof(f95,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f62])).
% 1.50/0.56  fof(f62,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) & r2_hidden(sK8(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.50/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f60,f61])).
% 1.50/0.56  fof(f61,plain,(
% 1.50/0.56    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) & r2_hidden(sK8(X0,X1,X2),k2_relat_1(X2))))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f60,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.50/0.56    inference(rectify,[],[f59])).
% 1.50/0.56  fof(f59,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.50/0.56    inference(nnf_transformation,[],[f34])).
% 1.50/0.56  fof(f34,plain,(
% 1.50/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.50/0.56    inference(ennf_transformation,[],[f18])).
% 1.50/0.56  fof(f18,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 1.50/0.56  fof(f785,plain,(
% 1.50/0.56    r2_hidden(k4_tarski(sK7(sK1,sK3(k2_relat_1(sK1),sK0)),sK3(k2_relat_1(sK1),sK0)),sK1) | ~spl9_52),
% 1.50/0.56    inference(avatar_component_clause,[],[f783])).
% 1.50/0.56  fof(f783,plain,(
% 1.50/0.56    spl9_52 <=> r2_hidden(k4_tarski(sK7(sK1,sK3(k2_relat_1(sK1),sK0)),sK3(k2_relat_1(sK1),sK0)),sK1)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).
% 1.50/0.56  fof(f224,plain,(
% 1.50/0.56    r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | ~spl9_13),
% 1.50/0.56    inference(avatar_component_clause,[],[f222])).
% 1.50/0.56  fof(f222,plain,(
% 1.50/0.56    spl9_13 <=> r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.50/0.56  fof(f219,plain,(
% 1.50/0.56    r2_hidden(sK3(k2_relat_1(sK1),sK0),sK0) | ~spl9_12),
% 1.50/0.56    inference(avatar_component_clause,[],[f217])).
% 1.50/0.56  fof(f217,plain,(
% 1.50/0.56    spl9_12 <=> r2_hidden(sK3(k2_relat_1(sK1),sK0),sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.50/0.56  fof(f119,plain,(
% 1.50/0.56    v1_relat_1(sK1) | ~spl9_3),
% 1.50/0.56    inference(avatar_component_clause,[],[f117])).
% 1.50/0.56  fof(f117,plain,(
% 1.50/0.56    spl9_3 <=> v1_relat_1(sK1)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.50/0.56  fof(f786,plain,(
% 1.50/0.56    spl9_52 | ~spl9_13),
% 1.50/0.56    inference(avatar_split_clause,[],[f753,f222,f783])).
% 1.50/0.56  fof(f753,plain,(
% 1.50/0.56    r2_hidden(k4_tarski(sK7(sK1,sK3(k2_relat_1(sK1),sK0)),sK3(k2_relat_1(sK1),sK0)),sK1) | ~spl9_13),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f224,f105])).
% 1.50/0.56  fof(f105,plain,(
% 1.50/0.56    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.50/0.56    inference(equality_resolution,[],[f88])).
% 1.50/0.56  fof(f88,plain,(
% 1.50/0.56    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f58])).
% 1.50/0.56  fof(f58,plain,(
% 1.50/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.50/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f54,f57,f56,f55])).
% 1.50/0.56  fof(f55,plain,(
% 1.50/0.56    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f56,plain,(
% 1.50/0.56    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f57,plain,(
% 1.50/0.56    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f54,plain,(
% 1.50/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.50/0.56    inference(rectify,[],[f53])).
% 1.50/0.56  fof(f53,plain,(
% 1.50/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.50/0.56    inference(nnf_transformation,[],[f17])).
% 1.50/0.56  fof(f17,axiom,(
% 1.50/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.50/0.56  fof(f728,plain,(
% 1.50/0.56    k2_relat_1(k1_xboole_0) != k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)) | k1_xboole_0 != k2_relat_1(k1_xboole_0) | k10_relat_1(sK1,sK0) != k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) | k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.50/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.50/0.56  fof(f642,plain,(
% 1.50/0.56    spl9_13 | spl9_2),
% 1.50/0.56    inference(avatar_split_clause,[],[f630,f111,f222])).
% 1.50/0.56  fof(f111,plain,(
% 1.50/0.56    spl9_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.50/0.56  fof(f630,plain,(
% 1.50/0.56    r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | spl9_2),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f113,f78])).
% 1.50/0.56  fof(f78,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f47])).
% 1.50/0.56  fof(f47,plain,(
% 1.50/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.50/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f46])).
% 1.50/0.56  fof(f46,plain,(
% 1.50/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f30,plain,(
% 1.50/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.50/0.56    inference(ennf_transformation,[],[f25])).
% 1.50/0.56  fof(f25,plain,(
% 1.50/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.50/0.56    inference(rectify,[],[f2])).
% 1.50/0.56  fof(f2,axiom,(
% 1.50/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.50/0.56  fof(f113,plain,(
% 1.50/0.56    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl9_2),
% 1.50/0.56    inference(avatar_component_clause,[],[f111])).
% 1.50/0.56  fof(f641,plain,(
% 1.50/0.56    spl9_12 | spl9_2),
% 1.50/0.56    inference(avatar_split_clause,[],[f631,f111,f217])).
% 1.50/0.56  fof(f631,plain,(
% 1.50/0.56    r2_hidden(sK3(k2_relat_1(sK1),sK0),sK0) | spl9_2),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f113,f79])).
% 1.50/0.56  fof(f79,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f47])).
% 1.50/0.56  fof(f619,plain,(
% 1.50/0.56    spl9_39 | ~spl9_3 | ~spl9_7),
% 1.50/0.56    inference(avatar_split_clause,[],[f608,f161,f117,f616])).
% 1.50/0.56  fof(f616,plain,(
% 1.50/0.56    spl9_39 <=> k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 1.50/0.56  fof(f161,plain,(
% 1.50/0.56    spl9_7 <=> k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.50/0.56  fof(f608,plain,(
% 1.50/0.56    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) | (~spl9_3 | ~spl9_7)),
% 1.50/0.56    inference(superposition,[],[f123,f163])).
% 1.50/0.56  fof(f163,plain,(
% 1.50/0.56    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0) | ~spl9_7),
% 1.50/0.56    inference(avatar_component_clause,[],[f161])).
% 1.50/0.56  fof(f123,plain,(
% 1.50/0.56    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0)))) ) | ~spl9_3),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f119,f102])).
% 1.50/0.56  fof(f102,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.50/0.56    inference(definition_unfolding,[],[f81,f75])).
% 1.50/0.56  fof(f81,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f31])).
% 1.50/0.56  fof(f31,plain,(
% 1.50/0.56    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f19])).
% 1.50/0.56  fof(f19,axiom,(
% 1.50/0.56    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 1.50/0.56  fof(f480,plain,(
% 1.50/0.56    spl9_25 | ~spl9_2 | ~spl9_6 | ~spl9_7),
% 1.50/0.56    inference(avatar_split_clause,[],[f454,f161,f156,f111,f477])).
% 1.50/0.56  fof(f477,plain,(
% 1.50/0.56    spl9_25 <=> k2_relat_1(k1_xboole_0) = k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 1.50/0.56  fof(f454,plain,(
% 1.50/0.56    k2_relat_1(k1_xboole_0) = k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)) | (~spl9_2 | ~spl9_6 | ~spl9_7)),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f187,f444,f90])).
% 1.50/0.56  fof(f90,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f58])).
% 1.50/0.56  fof(f444,plain,(
% 1.50/0.56    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))) ) | (~spl9_2 | ~spl9_7)),
% 1.50/0.56    inference(forward_demodulation,[],[f145,f163])).
% 1.50/0.56  fof(f145,plain,(
% 1.50/0.56    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),sK0)))) ) | ~spl9_2),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f112,f100])).
% 1.50/0.56  fof(f112,plain,(
% 1.50/0.56    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl9_2),
% 1.50/0.56    inference(avatar_component_clause,[],[f111])).
% 1.50/0.56  fof(f300,plain,(
% 1.50/0.56    spl9_14 | ~spl9_6),
% 1.50/0.56    inference(avatar_split_clause,[],[f277,f156,f296])).
% 1.50/0.56  fof(f296,plain,(
% 1.50/0.56    spl9_14 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.50/0.56  fof(f277,plain,(
% 1.50/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl9_6),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f187,f187,f90])).
% 1.50/0.56  fof(f253,plain,(
% 1.50/0.56    spl9_7 | ~spl9_2),
% 1.50/0.56    inference(avatar_split_clause,[],[f242,f111,f161])).
% 1.50/0.56  fof(f242,plain,(
% 1.50/0.56    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0) | ~spl9_2),
% 1.50/0.56    inference(resolution,[],[f112,f86])).
% 1.50/0.56  fof(f86,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f52])).
% 1.50/0.56  fof(f141,plain,(
% 1.50/0.56    spl9_5 | ~spl9_3),
% 1.50/0.56    inference(avatar_split_clause,[],[f124,f117,f137])).
% 1.50/0.56  fof(f137,plain,(
% 1.50/0.56    spl9_5 <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.50/0.56  fof(f124,plain,(
% 1.50/0.56    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | ~spl9_3),
% 1.50/0.56    inference(resolution,[],[f119,f71])).
% 1.50/0.56  fof(f71,plain,(
% 1.50/0.56    ( ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f27])).
% 1.50/0.56  fof(f27,plain,(
% 1.50/0.56    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f20])).
% 1.50/0.56  fof(f20,axiom,(
% 1.50/0.56    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).
% 1.50/0.56  fof(f120,plain,(
% 1.50/0.56    spl9_3),
% 1.50/0.56    inference(avatar_split_clause,[],[f63,f117])).
% 1.50/0.56  fof(f63,plain,(
% 1.50/0.56    v1_relat_1(sK1)),
% 1.50/0.56    inference(cnf_transformation,[],[f43])).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.50/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f42])).
% 1.50/0.56  fof(f42,plain,(
% 1.50/0.56    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f41,plain,(
% 1.50/0.56    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.50/0.56    inference(flattening,[],[f40])).
% 1.50/0.56  fof(f40,plain,(
% 1.50/0.56    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.50/0.56    inference(nnf_transformation,[],[f26])).
% 1.50/0.56  fof(f26,plain,(
% 1.50/0.56    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f23])).
% 1.50/0.56  fof(f23,negated_conjecture,(
% 1.50/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.50/0.56    inference(negated_conjecture,[],[f22])).
% 1.50/0.56  fof(f22,conjecture,(
% 1.50/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 1.50/0.56  fof(f115,plain,(
% 1.50/0.56    spl9_1 | spl9_2),
% 1.50/0.56    inference(avatar_split_clause,[],[f64,f111,f107])).
% 1.50/0.56  fof(f64,plain,(
% 1.50/0.56    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f43])).
% 1.50/0.56  fof(f114,plain,(
% 1.50/0.56    ~spl9_1 | ~spl9_2),
% 1.50/0.56    inference(avatar_split_clause,[],[f65,f111,f107])).
% 1.50/0.56  fof(f65,plain,(
% 1.50/0.56    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f43])).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (30658)------------------------------
% 1.50/0.56  % (30658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (30658)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (30658)Memory used [KB]: 7036
% 1.50/0.56  % (30658)Time elapsed: 0.142 s
% 1.50/0.56  % (30658)------------------------------
% 1.50/0.56  % (30658)------------------------------
% 1.50/0.56  % (30629)Success in time 0.203 s
%------------------------------------------------------------------------------
