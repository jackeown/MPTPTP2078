%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:09 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 125 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  250 ( 437 expanded)
%              Number of equality atoms :   39 (  89 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f81,f89,f91,f110,f252,f276,f278])).

fof(f278,plain,
    ( ~ spl7_4
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(resolution,[],[f275,f88])).

fof(f88,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl7_4
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f275,plain,
    ( r2_hidden(sK6(sK1,sK0),k1_xboole_0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl7_7
  <=> r2_hidden(sK6(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f276,plain,
    ( ~ spl7_5
    | spl7_7
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f271,f77,f73,f273,f102])).

fof(f102,plain,
    ( spl7_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f73,plain,
    ( spl7_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f77,plain,
    ( spl7_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f271,plain,
    ( r2_hidden(sK6(sK1,sK0),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f269,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f269,plain,
    ( r2_hidden(sK6(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f253,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f253,plain,
    ( r2_hidden(k4_tarski(sK0,sK6(sK1,sK0)),sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f74,f70])).

fof(f70,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f33,f36,f35,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f74,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f252,plain,
    ( spl7_1
    | spl7_2
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl7_1
    | spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f249,f75])).

fof(f75,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f249,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | spl7_2
    | ~ spl7_4 ),
    inference(trivial_inequality_removal,[],[f243])).

fof(f243,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,k1_relat_1(sK1))
    | spl7_2
    | ~ spl7_4 ),
    inference(superposition,[],[f78,f236])).

fof(f236,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k11_relat_1(sK1,X3)
        | r2_hidden(X3,k1_relat_1(sK1)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f233,f69])).

fof(f69,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f233,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK3(k11_relat_1(sK1,X0),k1_xboole_0)),sK1)
        | k1_xboole_0 = k11_relat_1(sK1,X0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f125,f41])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f125,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(X4)
        | r2_hidden(k4_tarski(X5,sK3(k11_relat_1(X4,X5),k1_xboole_0)),X4)
        | k1_xboole_0 = k11_relat_1(X4,X5) )
    | ~ spl7_4 ),
    inference(resolution,[],[f117,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f117,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(X3,k1_xboole_0),X3)
        | k1_xboole_0 = X3 )
    | ~ spl7_4 ),
    inference(resolution,[],[f52,f88])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f78,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f110,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl7_5 ),
    inference(resolution,[],[f104,f41])).

fof(f104,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f91,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl7_3 ),
    inference(resolution,[],[f85,f44])).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f85,plain,
    ( ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_3
  <=> ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f89,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f82,f87,f84])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f49,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f81,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f42,f77,f73])).

fof(f42,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f43,f77,f73])).

fof(f43,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (26697)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.56  % (26691)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.56  % (26689)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.56  % (26707)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.57  % (26697)Refutation found. Thanks to Tanya!
% 1.33/0.57  % SZS status Theorem for theBenchmark
% 1.64/0.58  % (26699)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.64/0.58  % (26707)Refutation not found, incomplete strategy% (26707)------------------------------
% 1.64/0.58  % (26707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (26707)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (26707)Memory used [KB]: 10746
% 1.64/0.58  % (26707)Time elapsed: 0.147 s
% 1.64/0.58  % (26707)------------------------------
% 1.64/0.58  % (26707)------------------------------
% 1.64/0.58  % (26705)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.64/0.58  % SZS output start Proof for theBenchmark
% 1.64/0.58  fof(f279,plain,(
% 1.64/0.58    $false),
% 1.64/0.58    inference(avatar_sat_refutation,[],[f80,f81,f89,f91,f110,f252,f276,f278])).
% 1.64/0.58  fof(f278,plain,(
% 1.64/0.58    ~spl7_4 | ~spl7_7),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f277])).
% 1.64/0.58  fof(f277,plain,(
% 1.64/0.58    $false | (~spl7_4 | ~spl7_7)),
% 1.64/0.58    inference(resolution,[],[f275,f88])).
% 1.64/0.58  fof(f88,plain,(
% 1.64/0.58    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl7_4),
% 1.64/0.58    inference(avatar_component_clause,[],[f87])).
% 1.64/0.58  fof(f87,plain,(
% 1.64/0.58    spl7_4 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.64/0.58  fof(f275,plain,(
% 1.64/0.58    r2_hidden(sK6(sK1,sK0),k1_xboole_0) | ~spl7_7),
% 1.64/0.58    inference(avatar_component_clause,[],[f273])).
% 1.64/0.58  fof(f273,plain,(
% 1.64/0.58    spl7_7 <=> r2_hidden(sK6(sK1,sK0),k1_xboole_0)),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.64/0.58  fof(f276,plain,(
% 1.64/0.58    ~spl7_5 | spl7_7 | ~spl7_1 | ~spl7_2),
% 1.64/0.58    inference(avatar_split_clause,[],[f271,f77,f73,f273,f102])).
% 1.64/0.58  fof(f102,plain,(
% 1.64/0.58    spl7_5 <=> v1_relat_1(sK1)),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.64/0.58  fof(f73,plain,(
% 1.64/0.58    spl7_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.64/0.58  fof(f77,plain,(
% 1.64/0.58    spl7_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.64/0.58  fof(f271,plain,(
% 1.64/0.58    r2_hidden(sK6(sK1,sK0),k1_xboole_0) | ~v1_relat_1(sK1) | (~spl7_1 | ~spl7_2)),
% 1.64/0.58    inference(forward_demodulation,[],[f269,f79])).
% 1.64/0.58  fof(f79,plain,(
% 1.64/0.58    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl7_2),
% 1.64/0.58    inference(avatar_component_clause,[],[f77])).
% 1.64/0.58  fof(f269,plain,(
% 1.64/0.58    r2_hidden(sK6(sK1,sK0),k11_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl7_1),
% 1.64/0.58    inference(resolution,[],[f253,f60])).
% 1.64/0.58  fof(f60,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f38])).
% 1.64/0.58  fof(f38,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 1.64/0.58    inference(nnf_transformation,[],[f20])).
% 1.64/0.58  fof(f20,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.64/0.58    inference(ennf_transformation,[],[f11])).
% 1.64/0.58  fof(f11,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 1.64/0.58  fof(f253,plain,(
% 1.64/0.58    r2_hidden(k4_tarski(sK0,sK6(sK1,sK0)),sK1) | ~spl7_1),
% 1.64/0.58    inference(resolution,[],[f74,f70])).
% 1.64/0.58  fof(f70,plain,(
% 1.64/0.58    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)) )),
% 1.64/0.58    inference(equality_resolution,[],[f56])).
% 1.64/0.58  fof(f56,plain,(
% 1.64/0.58    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.64/0.58    inference(cnf_transformation,[],[f37])).
% 1.64/0.58  fof(f37,plain,(
% 1.64/0.58    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f33,f36,f35,f34])).
% 1.64/0.58  fof(f34,plain,(
% 1.64/0.58    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f35,plain,(
% 1.64/0.58    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f36,plain,(
% 1.64/0.58    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f33,plain,(
% 1.64/0.58    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.64/0.58    inference(rectify,[],[f32])).
% 1.64/0.58  fof(f32,plain,(
% 1.64/0.58    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.64/0.58    inference(nnf_transformation,[],[f9])).
% 1.64/0.58  fof(f9,axiom,(
% 1.64/0.58    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.64/0.58  fof(f74,plain,(
% 1.64/0.58    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl7_1),
% 1.64/0.58    inference(avatar_component_clause,[],[f73])).
% 1.64/0.58  fof(f252,plain,(
% 1.64/0.58    spl7_1 | spl7_2 | ~spl7_4),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f250])).
% 1.64/0.58  fof(f250,plain,(
% 1.64/0.58    $false | (spl7_1 | spl7_2 | ~spl7_4)),
% 1.64/0.58    inference(resolution,[],[f249,f75])).
% 1.64/0.58  fof(f75,plain,(
% 1.64/0.58    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl7_1),
% 1.64/0.58    inference(avatar_component_clause,[],[f73])).
% 1.64/0.58  fof(f249,plain,(
% 1.64/0.58    r2_hidden(sK0,k1_relat_1(sK1)) | (spl7_2 | ~spl7_4)),
% 1.64/0.58    inference(trivial_inequality_removal,[],[f243])).
% 1.64/0.58  fof(f243,plain,(
% 1.64/0.58    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,k1_relat_1(sK1)) | (spl7_2 | ~spl7_4)),
% 1.64/0.58    inference(superposition,[],[f78,f236])).
% 1.64/0.58  fof(f236,plain,(
% 1.64/0.58    ( ! [X3] : (k1_xboole_0 = k11_relat_1(sK1,X3) | r2_hidden(X3,k1_relat_1(sK1))) ) | ~spl7_4),
% 1.64/0.58    inference(resolution,[],[f233,f69])).
% 1.64/0.58  fof(f69,plain,(
% 1.64/0.58    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 1.64/0.58    inference(equality_resolution,[],[f57])).
% 1.64/0.58  fof(f57,plain,(
% 1.64/0.58    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.64/0.58    inference(cnf_transformation,[],[f37])).
% 1.64/0.58  fof(f233,plain,(
% 1.64/0.58    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK3(k11_relat_1(sK1,X0),k1_xboole_0)),sK1) | k1_xboole_0 = k11_relat_1(sK1,X0)) ) | ~spl7_4),
% 1.64/0.58    inference(resolution,[],[f125,f41])).
% 1.64/0.58  fof(f41,plain,(
% 1.64/0.58    v1_relat_1(sK1)),
% 1.64/0.58    inference(cnf_transformation,[],[f24])).
% 1.64/0.58  fof(f24,plain,(
% 1.64/0.58    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.64/0.58  fof(f23,plain,(
% 1.64/0.58    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f22,plain,(
% 1.64/0.58    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.64/0.58    inference(flattening,[],[f21])).
% 1.64/0.58  fof(f21,plain,(
% 1.64/0.58    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 1.64/0.58    inference(nnf_transformation,[],[f15])).
% 1.64/0.58  fof(f15,plain,(
% 1.64/0.58    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f13])).
% 1.64/0.58  fof(f13,negated_conjecture,(
% 1.64/0.58    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.64/0.58    inference(negated_conjecture,[],[f12])).
% 1.64/0.58  fof(f12,conjecture,(
% 1.64/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 1.64/0.58  fof(f125,plain,(
% 1.64/0.58    ( ! [X4,X5] : (~v1_relat_1(X4) | r2_hidden(k4_tarski(X5,sK3(k11_relat_1(X4,X5),k1_xboole_0)),X4) | k1_xboole_0 = k11_relat_1(X4,X5)) ) | ~spl7_4),
% 1.64/0.58    inference(resolution,[],[f117,f61])).
% 1.64/0.58  fof(f61,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f38])).
% 1.64/0.58  fof(f117,plain,(
% 1.64/0.58    ( ! [X3] : (r2_hidden(sK3(X3,k1_xboole_0),X3) | k1_xboole_0 = X3) ) | ~spl7_4),
% 1.64/0.58    inference(resolution,[],[f52,f88])).
% 1.64/0.58  fof(f52,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | X0 = X1 | r2_hidden(sK3(X0,X1),X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f30,plain,(
% 1.64/0.58    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 1.64/0.58  fof(f29,plain,(
% 1.64/0.58    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f28,plain,(
% 1.64/0.58    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.64/0.58    inference(nnf_transformation,[],[f19])).
% 1.64/0.58  fof(f19,plain,(
% 1.64/0.58    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.64/0.58    inference(ennf_transformation,[],[f1])).
% 1.64/0.58  fof(f1,axiom,(
% 1.64/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.64/0.58  fof(f78,plain,(
% 1.64/0.58    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl7_2),
% 1.64/0.58    inference(avatar_component_clause,[],[f77])).
% 1.64/0.58  fof(f110,plain,(
% 1.64/0.58    spl7_5),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f109])).
% 1.64/0.58  fof(f109,plain,(
% 1.64/0.58    $false | spl7_5),
% 1.64/0.58    inference(resolution,[],[f104,f41])).
% 1.64/0.58  fof(f104,plain,(
% 1.64/0.58    ~v1_relat_1(sK1) | spl7_5),
% 1.64/0.58    inference(avatar_component_clause,[],[f102])).
% 1.64/0.58  fof(f91,plain,(
% 1.64/0.58    ~spl7_3),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f90])).
% 1.64/0.58  fof(f90,plain,(
% 1.64/0.58    $false | ~spl7_3),
% 1.64/0.58    inference(resolution,[],[f85,f44])).
% 1.64/0.58  fof(f44,plain,(
% 1.64/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f4])).
% 1.64/0.58  fof(f4,axiom,(
% 1.64/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.64/0.58  fof(f85,plain,(
% 1.64/0.58    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl7_3),
% 1.64/0.58    inference(avatar_component_clause,[],[f84])).
% 1.64/0.58  fof(f84,plain,(
% 1.64/0.58    spl7_3 <=> ! [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.64/0.58  fof(f89,plain,(
% 1.64/0.58    spl7_3 | spl7_4),
% 1.64/0.58    inference(avatar_split_clause,[],[f82,f87,f84])).
% 1.64/0.58  fof(f82,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.64/0.58    inference(superposition,[],[f49,f45])).
% 1.64/0.58  fof(f45,plain,(
% 1.64/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f3])).
% 1.64/0.58  fof(f3,axiom,(
% 1.64/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.64/0.58  fof(f49,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f26])).
% 1.64/0.58  fof(f26,plain,(
% 1.64/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f25])).
% 1.64/0.58  fof(f25,plain,(
% 1.64/0.58    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f17,plain,(
% 1.64/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.64/0.58    inference(ennf_transformation,[],[f14])).
% 1.64/0.58  fof(f14,plain,(
% 1.64/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.64/0.58    inference(rectify,[],[f2])).
% 1.64/0.58  fof(f2,axiom,(
% 1.64/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.64/0.58  fof(f81,plain,(
% 1.64/0.58    spl7_1 | ~spl7_2),
% 1.64/0.58    inference(avatar_split_clause,[],[f42,f77,f73])).
% 1.64/0.58  fof(f42,plain,(
% 1.64/0.58    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 1.64/0.58    inference(cnf_transformation,[],[f24])).
% 1.64/0.58  fof(f80,plain,(
% 1.64/0.58    ~spl7_1 | spl7_2),
% 1.64/0.58    inference(avatar_split_clause,[],[f43,f77,f73])).
% 1.64/0.58  fof(f43,plain,(
% 1.64/0.58    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 1.64/0.58    inference(cnf_transformation,[],[f24])).
% 1.64/0.58  % SZS output end Proof for theBenchmark
% 1.64/0.58  % (26697)------------------------------
% 1.64/0.58  % (26697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (26697)Termination reason: Refutation
% 1.64/0.58  
% 1.64/0.58  % (26697)Memory used [KB]: 6396
% 1.64/0.58  % (26697)Time elapsed: 0.134 s
% 1.64/0.58  % (26697)------------------------------
% 1.64/0.58  % (26697)------------------------------
% 1.64/0.59  % (26684)Success in time 0.225 s
%------------------------------------------------------------------------------
