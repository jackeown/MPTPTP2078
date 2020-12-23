%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t205_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:58 EDT 2019

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 185 expanded)
%              Number of leaves         :   16 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  252 ( 718 expanded)
%              Number of equality atoms :   41 ( 124 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3865,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f81,f322,f3682,f3864])).

fof(f3864,plain,
    ( ~ spl7_0
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f3848])).

fof(f3848,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(resolution,[],[f3824,f50])).

fof(f50,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',dt_o_0_0_xboole_0)).

fof(f3824,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f3823])).

fof(f3823,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(superposition,[],[f3764,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',t6_boole)).

fof(f3764,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f3763,f47])).

fof(f47,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k11_relat_1(sK1,sK0) = k1_xboole_0
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k11_relat_1(sK1,sK0) != k1_xboole_0
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( k11_relat_1(X1,X0) = k1_xboole_0
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k11_relat_1(X1,X0) != k1_xboole_0
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k11_relat_1(sK1,sK0) = k1_xboole_0
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k11_relat_1(sK1,sK0) != k1_xboole_0
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k11_relat_1(X1,X0) = k1_xboole_0
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k11_relat_1(X1,X0) != k1_xboole_0
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k11_relat_1(X1,X0) = k1_xboole_0
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k11_relat_1(X1,X0) != k1_xboole_0
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k11_relat_1(X1,X0) != k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k11_relat_1(X1,X0) != k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k11_relat_1(X1,X0) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',t205_relat_1)).

fof(f3763,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f3701,f77])).

fof(f77,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl7_0
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f3701,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_2 ),
    inference(superposition,[],[f122,f73])).

fof(f73,plain,
    ( k11_relat_1(sK1,sK0) = k1_xboole_0
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_2
  <=> k11_relat_1(sK1,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f122,plain,(
    ! [X6,X7] :
      ( ~ v1_xboole_0(k11_relat_1(X6,X7))
      | ~ r2_hidden(X7,k1_relat_1(X6))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f96,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',d1_xboole_0)).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),k11_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f64,f67])).

fof(f67,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f41,f44,f43,f42])).

fof(f42,plain,(
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

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',d4_relat_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',t204_relat_1)).

fof(f3682,plain,
    ( spl7_10
    | spl7_10
    | spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f3681,f79,f69,f296,f296])).

fof(f296,plain,
    ( spl7_10
  <=> ! [X4] : ~ v1_xboole_0(X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f69,plain,
    ( spl7_1
  <=> ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f79,plain,
    ( spl7_3
  <=> k11_relat_1(sK1,sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f3681,plain,
    ( ! [X33,X34] :
        ( ~ v1_xboole_0(X33)
        | ~ v1_xboole_0(X34) )
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f3680,f100])).

fof(f100,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f92,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k1_relat_1(X7))
      | ~ v1_xboole_0(X7) ) ),
    inference(resolution,[],[f67,f52])).

fof(f3680,plain,
    ( ! [X33,X34] :
        ( ~ v1_xboole_0(k1_relat_1(X33))
        | ~ v1_xboole_0(X33)
        | ~ v1_xboole_0(X34) )
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f3646,f51])).

fof(f3646,plain,
    ( ! [X33,X34] :
        ( k1_xboole_0 != X34
        | ~ v1_xboole_0(k1_relat_1(X33))
        | ~ v1_xboole_0(X33)
        | ~ v1_xboole_0(X34) )
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(superposition,[],[f3170,f386])).

fof(f386,plain,(
    ! [X6,X5] :
      ( k1_relat_1(k1_relat_1(X5)) = X6
      | ~ v1_xboole_0(X5)
      | ~ v1_xboole_0(X6) ) ),
    inference(resolution,[],[f110,f52])).

fof(f110,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK4(k1_relat_1(X12),X13),X13)
      | k1_relat_1(k1_relat_1(X12)) = X13
      | ~ v1_xboole_0(X12) ) ),
    inference(resolution,[],[f60,f92])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3170,plain,
    ( ! [X217] :
        ( k1_relat_1(X217) != k1_xboole_0
        | ~ v1_xboole_0(X217) )
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f3169,f70])).

fof(f70,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f3169,plain,
    ( ! [X217] :
        ( k1_relat_1(X217) != k1_xboole_0
        | ~ v1_xboole_0(X217)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f2994,f47])).

fof(f2994,plain,
    ( ! [X217] :
        ( k1_relat_1(X217) != k1_xboole_0
        | ~ v1_xboole_0(X217)
        | ~ v1_relat_1(sK1)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
    | ~ spl7_3 ),
    inference(superposition,[],[f80,f473])).

fof(f473,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X3) = k11_relat_1(X4,X5)
      | ~ v1_xboole_0(X3)
      | ~ v1_relat_1(X4)
      | r2_hidden(X5,k1_relat_1(X4)) ) ),
    inference(resolution,[],[f118,f66])).

fof(f66,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f118,plain,(
    ! [X10,X8,X9] :
      ( r2_hidden(k4_tarski(X10,sK4(X8,k11_relat_1(X9,X10))),X9)
      | ~ v1_xboole_0(X8)
      | k1_relat_1(X8) = k11_relat_1(X9,X10)
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f109,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f109,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK4(X10,X11),X11)
      | k1_relat_1(X10) = X11
      | ~ v1_xboole_0(X10) ) ),
    inference(resolution,[],[f60,f52])).

fof(f80,plain,
    ( k11_relat_1(sK1,sK0) != k1_xboole_0
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f322,plain,(
    ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl7_10 ),
    inference(resolution,[],[f297,f50])).

fof(f297,plain,
    ( ! [X4] : ~ v1_xboole_0(X4)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f296])).

fof(f81,plain,
    ( spl7_0
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f48,f79,f76])).

fof(f48,plain,
    ( k11_relat_1(sK1,sK0) != k1_xboole_0
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f49,f72,f69])).

fof(f49,plain,
    ( k11_relat_1(sK1,sK0) = k1_xboole_0
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
