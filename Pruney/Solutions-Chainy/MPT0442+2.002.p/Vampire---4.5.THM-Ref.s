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
% DateTime   : Thu Dec  3 12:46:59 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 311 expanded)
%              Number of leaves         :   18 ( 102 expanded)
%              Depth                    :   15
%              Number of atoms          :  335 (1688 expanded)
%              Number of equality atoms :   33 ( 130 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f576,f601,f603,f787,f1126])).

fof(f1126,plain,
    ( spl7_12
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f1125])).

fof(f1125,plain,
    ( $false
    | spl7_12
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1102,f570])).

fof(f570,plain,
    ( r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl7_16
  <=> r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f1102,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1)
    | spl7_12 ),
    inference(unit_resulting_resolution,[],[f528,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & ~ r2_hidden(sK6(X0,X1,X2),X0) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & ~ r2_hidden(sK6(X0,X1,X2),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f528,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),k2_xboole_0(sK1,sK1))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f526])).

fof(f526,plain,
    ( spl7_12
  <=> r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),k2_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f787,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f786])).

fof(f786,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f774,f674])).

fof(f674,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k2_relat_1(sK0),k2_relat_1(sK1))),sK1)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f627,f51])).

fof(f51,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f627,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f63,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f63,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_2
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f774,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_relat_1(sK0),k2_relat_1(sK1))),sK1)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f33,f666,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f666,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_relat_1(sK0),k2_relat_1(sK1))),sK0)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f626,f52])).

fof(f52,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f626,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK0))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
      | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) )
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X1))
            | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(X1)) )
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X1))
          | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(X1)) )
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
        | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) )
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f603,plain,
    ( spl7_13
    | spl7_16
    | spl7_1
    | spl7_12 ),
    inference(avatar_split_clause,[],[f602,f526,f57,f568,f530])).

fof(f530,plain,
    ( spl7_13
  <=> r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f57,plain,
    ( spl7_1
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f602,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1)
    | r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK0)
    | spl7_12 ),
    inference(subsumption_resolution,[],[f564,f528])).

fof(f564,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1)
    | r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK0)
    | r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),k2_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f144,f245])).

fof(f245,plain,(
    k1_relat_1(sK1) = k1_relat_1(k2_xboole_0(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f244,f106])).

fof(f106,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X1),k1_relat_1(sK1))
      | k1_relat_1(k2_xboole_0(sK1,sK1)) = X1
      | ~ r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X1),X1) ) ),
    inference(superposition,[],[f70,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    k1_relat_1(k2_xboole_0(sK1,sK1)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f32,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f244,plain,
    ( r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1)),k1_relat_1(sK1))
    | k1_relat_1(sK1) = k1_relat_1(k2_xboole_0(sK1,sK1)) ),
    inference(factoring,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X0),k1_relat_1(sK1))
      | k1_relat_1(k2_xboole_0(sK1,sK1)) = X0
      | r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( k1_relat_1(k2_xboole_0(sK1,sK1)) = X0
      | r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X0),k1_relat_1(sK1))
      | r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X0),k1_relat_1(sK1))
      | r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X0),X0) ) ),
    inference(superposition,[],[f70,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f144,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(X0))
      | r2_hidden(sK6(sK0,sK1,X0),sK1)
      | r2_hidden(sK6(sK0,sK1,X0),sK0)
      | r2_hidden(sK6(sK0,sK1,X0),X0) ) ),
    inference(superposition,[],[f98,f48])).

fof(f98,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f36,f69])).

fof(f69,plain,(
    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f31,f32,f35])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f601,plain,
    ( spl7_16
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f595,f530,f568])).

fof(f595,plain,
    ( r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1)
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f33,f531,f38])).

fof(f531,plain,
    ( r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f530])).

fof(f576,plain,
    ( ~ spl7_12
    | spl7_1 ),
    inference(avatar_split_clause,[],[f575,f57,f526])).

fof(f575,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),k2_xboole_0(sK1,sK1))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f574,f55])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f574,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1)
    | ~ r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),k2_xboole_0(sK1,sK1))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f539,f59])).

fof(f59,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f539,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1)
    | ~ r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),k2_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f146,f245])).

fof(f146,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(X2))
      | ~ r2_hidden(sK6(sK0,sK1,X2),sK1)
      | ~ r2_hidden(sK6(sK0,sK1,X2),X2) ) ),
    inference(superposition,[],[f98,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f34,f61,f57])).

fof(f34,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:19:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (26484)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.53  % (26507)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.54  % (26488)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.55  % (26485)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.50/0.56  % (26482)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.50/0.56  % (26491)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.56  % (26500)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (26502)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.56  % (26498)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.56  % (26509)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.56  % (26493)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.57  % (26499)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.57  % (26496)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.57  % (26510)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.57  % (26495)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.57  % (26492)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.50/0.57  % (26480)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.50/0.57  % (26497)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.57  % (26506)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.50/0.58  % (26490)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.58  % (26483)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.58  % (26512)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.58  % (26505)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.50/0.58  % (26505)Refutation not found, incomplete strategy% (26505)------------------------------
% 1.50/0.58  % (26505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (26505)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.58  
% 1.50/0.58  % (26505)Memory used [KB]: 10618
% 1.50/0.58  % (26505)Time elapsed: 0.156 s
% 1.50/0.58  % (26505)------------------------------
% 1.50/0.58  % (26505)------------------------------
% 1.50/0.58  % (26486)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.50/0.58  % (26489)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.50/0.59  % (26511)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.59  % (26508)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.60  % (26494)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.50/0.60  % (26487)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.61  % (26501)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.11/0.67  % (26509)Refutation found. Thanks to Tanya!
% 2.11/0.67  % SZS status Theorem for theBenchmark
% 2.11/0.67  % SZS output start Proof for theBenchmark
% 2.11/0.67  fof(f1127,plain,(
% 2.11/0.67    $false),
% 2.11/0.67    inference(avatar_sat_refutation,[],[f64,f576,f601,f603,f787,f1126])).
% 2.11/0.67  fof(f1126,plain,(
% 2.11/0.67    spl7_12 | ~spl7_16),
% 2.11/0.67    inference(avatar_contradiction_clause,[],[f1125])).
% 2.11/0.67  fof(f1125,plain,(
% 2.11/0.67    $false | (spl7_12 | ~spl7_16)),
% 2.11/0.67    inference(subsumption_resolution,[],[f1102,f570])).
% 2.11/0.67  fof(f570,plain,(
% 2.11/0.67    r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1) | ~spl7_16),
% 2.11/0.67    inference(avatar_component_clause,[],[f568])).
% 2.11/0.67  fof(f568,plain,(
% 2.11/0.67    spl7_16 <=> r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1)),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.11/0.67  fof(f1102,plain,(
% 2.11/0.67    ~r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1) | spl7_12),
% 2.11/0.67    inference(unit_resulting_resolution,[],[f528,f54])).
% 2.11/0.67  fof(f54,plain,(
% 2.11/0.67    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 2.11/0.67    inference(equality_resolution,[],[f46])).
% 2.11/0.67  fof(f46,plain,(
% 2.11/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.11/0.67    inference(cnf_transformation,[],[f30])).
% 2.11/0.67  fof(f30,plain,(
% 2.11/0.67    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK6(X0,X1,X2),X1) & ~r2_hidden(sK6(X0,X1,X2),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.11/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 2.11/0.67  fof(f29,plain,(
% 2.11/0.67    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK6(X0,X1,X2),X1) & ~r2_hidden(sK6(X0,X1,X2),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f28,plain,(
% 2.11/0.67    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.11/0.67    inference(rectify,[],[f27])).
% 2.11/0.67  fof(f27,plain,(
% 2.11/0.67    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.11/0.67    inference(flattening,[],[f26])).
% 2.11/0.67  fof(f26,plain,(
% 2.11/0.67    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.11/0.67    inference(nnf_transformation,[],[f3])).
% 2.11/0.67  fof(f3,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.11/0.67  fof(f528,plain,(
% 2.11/0.67    ~r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),k2_xboole_0(sK1,sK1)) | spl7_12),
% 2.11/0.67    inference(avatar_component_clause,[],[f526])).
% 2.11/0.67  fof(f526,plain,(
% 2.11/0.67    spl7_12 <=> r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),k2_xboole_0(sK1,sK1))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.11/0.67  fof(f787,plain,(
% 2.11/0.67    spl7_2),
% 2.11/0.67    inference(avatar_contradiction_clause,[],[f786])).
% 2.11/0.67  fof(f786,plain,(
% 2.11/0.67    $false | spl7_2),
% 2.11/0.67    inference(subsumption_resolution,[],[f774,f674])).
% 2.11/0.67  fof(f674,plain,(
% 2.11/0.67    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK2(k2_relat_1(sK0),k2_relat_1(sK1))),sK1)) ) | spl7_2),
% 2.11/0.67    inference(unit_resulting_resolution,[],[f627,f51])).
% 2.11/0.67  fof(f51,plain,(
% 2.11/0.67    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 2.11/0.67    inference(equality_resolution,[],[f42])).
% 2.11/0.67  fof(f42,plain,(
% 2.11/0.67    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 2.11/0.67    inference(cnf_transformation,[],[f25])).
% 2.11/0.67  fof(f25,plain,(
% 2.11/0.67    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.11/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f24,f23,f22])).
% 2.11/0.67  fof(f22,plain,(
% 2.11/0.67    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f23,plain,(
% 2.11/0.67    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f24,plain,(
% 2.11/0.67    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f21,plain,(
% 2.11/0.67    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.11/0.67    inference(rectify,[],[f20])).
% 2.11/0.67  fof(f20,plain,(
% 2.11/0.67    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 2.11/0.67    inference(nnf_transformation,[],[f5])).
% 2.11/0.67  fof(f5,axiom,(
% 2.11/0.67    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 2.11/0.67  fof(f627,plain,(
% 2.11/0.67    ~r2_hidden(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | spl7_2),
% 2.11/0.67    inference(unit_resulting_resolution,[],[f63,f40])).
% 2.11/0.67  fof(f40,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f19])).
% 2.11/0.67  fof(f19,plain,(
% 2.11/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 2.11/0.67  fof(f18,plain,(
% 2.11/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f17,plain,(
% 2.11/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.67    inference(rectify,[],[f16])).
% 2.11/0.67  fof(f16,plain,(
% 2.11/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.67    inference(nnf_transformation,[],[f12])).
% 2.11/0.67  fof(f12,plain,(
% 2.11/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.11/0.67    inference(ennf_transformation,[],[f2])).
% 2.11/0.67  fof(f2,axiom,(
% 2.11/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.11/0.67  fof(f63,plain,(
% 2.11/0.67    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | spl7_2),
% 2.11/0.67    inference(avatar_component_clause,[],[f61])).
% 2.11/0.67  fof(f61,plain,(
% 2.11/0.67    spl7_2 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.11/0.67  fof(f774,plain,(
% 2.11/0.67    r2_hidden(k4_tarski(sK5(sK0,sK2(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_relat_1(sK0),k2_relat_1(sK1))),sK1) | spl7_2),
% 2.11/0.67    inference(unit_resulting_resolution,[],[f33,f666,f38])).
% 2.11/0.67  fof(f38,plain,(
% 2.11/0.67    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f19])).
% 2.11/0.67  fof(f666,plain,(
% 2.11/0.67    r2_hidden(k4_tarski(sK5(sK0,sK2(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_relat_1(sK0),k2_relat_1(sK1))),sK0) | spl7_2),
% 2.11/0.67    inference(unit_resulting_resolution,[],[f626,f52])).
% 2.11/0.67  fof(f52,plain,(
% 2.11/0.67    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 2.11/0.67    inference(equality_resolution,[],[f41])).
% 2.11/0.67  fof(f41,plain,(
% 2.11/0.67    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 2.11/0.67    inference(cnf_transformation,[],[f25])).
% 2.11/0.67  fof(f626,plain,(
% 2.11/0.67    r2_hidden(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK0)) | spl7_2),
% 2.11/0.67    inference(unit_resulting_resolution,[],[f63,f39])).
% 2.11/0.67  fof(f39,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f19])).
% 2.11/0.67  fof(f33,plain,(
% 2.11/0.67    r1_tarski(sK0,sK1)),
% 2.11/0.67    inference(cnf_transformation,[],[f15])).
% 2.11/0.67  fof(f15,plain,(
% 2.11/0.67    ((~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.11/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14,f13])).
% 2.11/0.67  fof(f13,plain,(
% 2.11/0.67    ? [X0] : (? [X1] : ((~r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : ((~r1_tarski(k2_relat_1(sK0),k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(X1))) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f14,plain,(
% 2.11/0.67    ? [X1] : ((~r1_tarski(k2_relat_1(sK0),k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(X1))) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => ((~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f10,plain,(
% 2.11/0.67    ? [X0] : (? [X1] : ((~r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.11/0.67    inference(flattening,[],[f9])).
% 2.11/0.67  fof(f9,plain,(
% 2.11/0.67    ? [X0] : (? [X1] : (((~r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.11/0.67    inference(ennf_transformation,[],[f8])).
% 2.11/0.67  fof(f8,negated_conjecture,(
% 2.11/0.67    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.11/0.67    inference(negated_conjecture,[],[f7])).
% 2.11/0.67  fof(f7,conjecture,(
% 2.11/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 2.11/0.67  fof(f603,plain,(
% 2.11/0.67    spl7_13 | spl7_16 | spl7_1 | spl7_12),
% 2.11/0.67    inference(avatar_split_clause,[],[f602,f526,f57,f568,f530])).
% 2.11/0.67  fof(f530,plain,(
% 2.11/0.67    spl7_13 <=> r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK0)),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.11/0.67  fof(f57,plain,(
% 2.11/0.67    spl7_1 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.11/0.67  fof(f602,plain,(
% 2.11/0.67    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1) | r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK0) | spl7_12),
% 2.11/0.67    inference(subsumption_resolution,[],[f564,f528])).
% 2.11/0.67  fof(f564,plain,(
% 2.11/0.67    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1) | r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK0) | r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),k2_xboole_0(sK1,sK1))),
% 2.11/0.67    inference(superposition,[],[f144,f245])).
% 2.11/0.67  fof(f245,plain,(
% 2.11/0.67    k1_relat_1(sK1) = k1_relat_1(k2_xboole_0(sK1,sK1))),
% 2.11/0.67    inference(subsumption_resolution,[],[f244,f106])).
% 2.11/0.67  fof(f106,plain,(
% 2.11/0.67    ( ! [X1] : (~r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X1),k1_relat_1(sK1)) | k1_relat_1(k2_xboole_0(sK1,sK1)) = X1 | ~r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X1),X1)) )),
% 2.11/0.67    inference(superposition,[],[f70,f49])).
% 2.11/0.67  fof(f49,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f30])).
% 2.11/0.67  fof(f70,plain,(
% 2.11/0.67    k1_relat_1(k2_xboole_0(sK1,sK1)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))),
% 2.11/0.67    inference(unit_resulting_resolution,[],[f32,f32,f35])).
% 2.11/0.67  fof(f35,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f11])).
% 2.11/0.67  fof(f11,plain,(
% 2.11/0.67    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.11/0.67    inference(ennf_transformation,[],[f6])).
% 2.11/0.67  fof(f6,axiom,(
% 2.11/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 2.11/0.67  fof(f32,plain,(
% 2.11/0.67    v1_relat_1(sK1)),
% 2.11/0.67    inference(cnf_transformation,[],[f15])).
% 2.11/0.67  fof(f244,plain,(
% 2.11/0.67    r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1)),k1_relat_1(sK1)) | k1_relat_1(sK1) = k1_relat_1(k2_xboole_0(sK1,sK1))),
% 2.11/0.67    inference(factoring,[],[f117])).
% 2.11/0.67  fof(f117,plain,(
% 2.11/0.67    ( ! [X0] : (r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X0),k1_relat_1(sK1)) | k1_relat_1(k2_xboole_0(sK1,sK1)) = X0 | r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X0),X0)) )),
% 2.11/0.67    inference(duplicate_literal_removal,[],[f105])).
% 2.11/0.67  fof(f105,plain,(
% 2.11/0.67    ( ! [X0] : (k1_relat_1(k2_xboole_0(sK1,sK1)) = X0 | r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X0),k1_relat_1(sK1)) | r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X0),k1_relat_1(sK1)) | r2_hidden(sK6(k1_relat_1(sK1),k1_relat_1(sK1),X0),X0)) )),
% 2.11/0.67    inference(superposition,[],[f70,f48])).
% 2.11/0.67  fof(f48,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f30])).
% 2.11/0.67  fof(f144,plain,(
% 2.11/0.67    ( ! [X0] : (r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) | r2_hidden(sK6(sK0,sK1,X0),sK1) | r2_hidden(sK6(sK0,sK1,X0),sK0) | r2_hidden(sK6(sK0,sK1,X0),X0)) )),
% 2.11/0.67    inference(superposition,[],[f98,f48])).
% 2.11/0.67  fof(f98,plain,(
% 2.11/0.67    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))),
% 2.11/0.67    inference(superposition,[],[f36,f69])).
% 2.11/0.67  fof(f69,plain,(
% 2.11/0.67    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.11/0.67    inference(unit_resulting_resolution,[],[f31,f32,f35])).
% 2.11/0.67  fof(f31,plain,(
% 2.11/0.67    v1_relat_1(sK0)),
% 2.11/0.67    inference(cnf_transformation,[],[f15])).
% 2.11/0.67  fof(f36,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f4])).
% 2.11/0.67  fof(f4,axiom,(
% 2.11/0.67    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.11/0.67  fof(f601,plain,(
% 2.11/0.67    spl7_16 | ~spl7_13),
% 2.11/0.67    inference(avatar_split_clause,[],[f595,f530,f568])).
% 2.11/0.67  fof(f595,plain,(
% 2.11/0.67    r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1) | ~spl7_13),
% 2.11/0.67    inference(unit_resulting_resolution,[],[f33,f531,f38])).
% 2.11/0.67  fof(f531,plain,(
% 2.11/0.67    r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK0) | ~spl7_13),
% 2.11/0.67    inference(avatar_component_clause,[],[f530])).
% 2.11/0.67  fof(f576,plain,(
% 2.11/0.67    ~spl7_12 | spl7_1),
% 2.11/0.67    inference(avatar_split_clause,[],[f575,f57,f526])).
% 2.11/0.67  fof(f575,plain,(
% 2.11/0.67    ~r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),k2_xboole_0(sK1,sK1)) | spl7_1),
% 2.11/0.67    inference(subsumption_resolution,[],[f574,f55])).
% 2.11/0.67  fof(f55,plain,(
% 2.11/0.67    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 2.11/0.67    inference(equality_resolution,[],[f45])).
% 2.11/0.67  fof(f45,plain,(
% 2.11/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.11/0.67    inference(cnf_transformation,[],[f30])).
% 2.11/0.67  fof(f574,plain,(
% 2.11/0.67    ~r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1) | ~r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),k2_xboole_0(sK1,sK1)) | spl7_1),
% 2.11/0.67    inference(subsumption_resolution,[],[f539,f59])).
% 2.11/0.67  fof(f59,plain,(
% 2.11/0.67    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | spl7_1),
% 2.11/0.67    inference(avatar_component_clause,[],[f57])).
% 2.11/0.67  fof(f539,plain,(
% 2.11/0.67    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),sK1) | ~r2_hidden(sK6(sK0,sK1,k2_xboole_0(sK1,sK1)),k2_xboole_0(sK1,sK1))),
% 2.11/0.67    inference(superposition,[],[f146,f245])).
% 2.11/0.67  fof(f146,plain,(
% 2.11/0.67    ( ! [X2] : (r1_tarski(k1_relat_1(sK0),k1_relat_1(X2)) | ~r2_hidden(sK6(sK0,sK1,X2),sK1) | ~r2_hidden(sK6(sK0,sK1,X2),X2)) )),
% 2.11/0.67    inference(superposition,[],[f98,f50])).
% 2.11/0.67  fof(f50,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f30])).
% 2.11/0.67  fof(f64,plain,(
% 2.11/0.67    ~spl7_1 | ~spl7_2),
% 2.11/0.67    inference(avatar_split_clause,[],[f34,f61,f57])).
% 2.11/0.67  fof(f34,plain,(
% 2.11/0.67    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.11/0.67    inference(cnf_transformation,[],[f15])).
% 2.11/0.67  % SZS output end Proof for theBenchmark
% 2.11/0.67  % (26509)------------------------------
% 2.11/0.67  % (26509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.67  % (26509)Termination reason: Refutation
% 2.11/0.67  
% 2.11/0.67  % (26509)Memory used [KB]: 11257
% 2.11/0.67  % (26509)Time elapsed: 0.263 s
% 2.11/0.67  % (26509)------------------------------
% 2.11/0.67  % (26509)------------------------------
% 2.48/0.70  % (26474)Success in time 0.342 s
%------------------------------------------------------------------------------
