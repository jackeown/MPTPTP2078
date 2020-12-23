%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:03 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 217 expanded)
%              Number of leaves         :   21 (  67 expanded)
%              Depth                    :   19
%              Number of atoms          :  341 ( 747 expanded)
%              Number of equality atoms :   46 ( 145 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f95,f97,f247,f288])).

fof(f288,plain,
    ( spl11_2
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f286,f47])).

fof(f47,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f286,plain,
    ( ~ v1_relat_1(sK3)
    | spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f284,f91])).

fof(f91,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl11_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f284,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | spl11_2
    | ~ spl11_4 ),
    inference(resolution,[],[f283,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f283,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f282,f47])).

fof(f282,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ v1_relat_1(sK3)
    | spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f281,f91])).

fof(f281,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | spl11_2
    | ~ spl11_4 ),
    inference(resolution,[],[f276,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f139,f68])).

fof(f139,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f74,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X2,X1,X0)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f17,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X4,X0,X3] :
      ( sP0(X1,X4,X0,X3)
    <=> ? [X5] :
          ( r2_hidden(k4_tarski(X5,X4),X1)
          & r2_hidden(k4_tarski(X3,X5),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X2)
        <=> sP0(X1,X4,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ( k5_relat_1(X0,X1) = X2
      <=> sP1(X0,X1,X2) )
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f74,plain,(
    ! [X2,X1] :
      ( ~ sP2(k5_relat_1(X2,X1),X1,X2)
      | sP1(X2,X1,k5_relat_1(X2,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | k5_relat_1(X2,X1) != X0
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( k5_relat_1(X2,X1) = X0
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | k5_relat_1(X2,X1) != X0 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ( ( k5_relat_1(X0,X1) = X2
          | ~ sP1(X0,X1,X2) )
        & ( sP1(X0,X1,X2)
          | k5_relat_1(X0,X1) != X2 ) )
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ sP1(sK3,k1_xboole_0,X0)
        | ~ v1_relat_1(X0) )
    | spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f275,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,k1_xboole_0,X1)
      | k1_xboole_0 = X1
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f179,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ sP1(X3,k1_xboole_0,X2) ) ),
    inference(resolution,[],[f175,f55])).

fof(f55,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( sP0(X1,X6,X0,X5)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK7(X0,X1,X2),X0,sK6(X0,X1,X2))
            | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
          & ( sP0(X1,sK7(X0,X1,X2),X0,sK6(X0,X1,X2))
            | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ sP0(X1,X6,X0,X5) )
            & ( sP0(X1,X6,X0,X5)
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ sP0(X1,X4,X0,X3)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( sP0(X1,X4,X0,X3)
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ sP0(X1,sK7(X0,X1,X2),X0,sK6(X0,X1,X2))
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( sP0(X1,sK7(X0,X1,X2),X0,sK6(X0,X1,X2))
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ sP0(X1,X4,X0,X3)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( sP0(X1,X4,X0,X3)
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ sP0(X1,X6,X0,X5) )
            & ( sP0(X1,X6,X0,X5)
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ sP0(X1,X4,X0,X3)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( sP0(X1,X4,X0,X3)
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X2)
              | ~ sP0(X1,X4,X0,X3) )
            & ( sP0(X1,X4,X0,X3)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f175,plain,(
    ! [X6,X7,X5] : ~ sP0(k1_xboole_0,X5,X6,X7) ),
    inference(resolution,[],[f60,f101])).

fof(f101,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f66,f50])).

fof(f50,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f18,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r2_hidden(k4_tarski(X4,X1),X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
      & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X1),X0)
          & r2_hidden(k4_tarski(X3,sK8(X0,X1,X2,X3)),X2) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f39])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(k4_tarski(X5,X1),X0)
          & r2_hidden(k4_tarski(X3,X5),X2) )
     => ( r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X1),X0)
        & r2_hidden(k4_tarski(X3,sK8(X0,X1,X2,X3)),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r2_hidden(k4_tarski(X4,X1),X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(X5,X1),X0)
            & r2_hidden(k4_tarski(X3,X5),X2) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X4,X0,X3] :
      ( ( sP0(X1,X4,X0,X3)
        | ! [X5] :
            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(X5,X4),X1)
            & r2_hidden(k4_tarski(X3,X5),X0) )
        | ~ sP0(X1,X4,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ sP1(sK3,k1_xboole_0,X0)
        | k1_xboole_0 != X0
        | ~ v1_relat_1(X0) )
    | spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f274,f47])).

fof(f274,plain,
    ( ! [X0] :
        ( ~ sP1(sK3,k1_xboole_0,X0)
        | k1_xboole_0 != X0
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK3) )
    | spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f273,f91])).

fof(f273,plain,
    ( ! [X0] :
        ( ~ sP1(sK3,k1_xboole_0,X0)
        | k1_xboole_0 != X0
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(sK3) )
    | spl11_2 ),
    inference(resolution,[],[f269,f62])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ sP2(X0,k1_xboole_0,sK3)
        | ~ sP1(sK3,k1_xboole_0,X0)
        | k1_xboole_0 != X0 )
    | spl11_2 ),
    inference(superposition,[],[f82,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,X1) = X0
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl11_2
  <=> k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f247,plain,
    ( spl11_1
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl11_1
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f245,f91])).

fof(f245,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl11_1
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f242,f47])).

fof(f242,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k1_xboole_0)
    | spl11_1
    | ~ spl11_4 ),
    inference(resolution,[],[f240,f68])).

fof(f240,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | spl11_1
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f239,f47])).

fof(f239,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | ~ v1_relat_1(sK3)
    | spl11_1
    | ~ spl11_4 ),
    inference(trivial_inequality_removal,[],[f232])).

fof(f232,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | ~ v1_relat_1(sK3)
    | spl11_1
    | ~ spl11_4 ),
    inference(superposition,[],[f78,f173])).

fof(f173,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f172,f91])).

fof(f172,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f169,f140])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ sP1(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X1
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f167,f52])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ sP1(k1_xboole_0,X3,X2) ) ),
    inference(resolution,[],[f163,f55])).

fof(f163,plain,(
    ! [X2,X0,X1] : ~ sP0(X0,X1,k1_xboole_0,X2) ),
    inference(resolution,[],[f59,f101])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK8(X0,X1,X2,X3)),X2)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl11_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f97,plain,
    ( spl11_3
    | spl11_4 ),
    inference(avatar_split_clause,[],[f96,f89,f86])).

fof(f86,plain,
    ( spl11_3
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f96,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f73,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f63,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f67,f63])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f95,plain,(
    ~ spl11_3 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f47,f87])).

fof(f87,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f83,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f48,f80,f76])).

fof(f48,plain,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:04:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (15488)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (15474)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (15492)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (15470)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (15469)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (15489)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (15479)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (15483)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (15484)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (15478)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (15496)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (15490)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (15471)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (15472)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (15473)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (15482)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (15481)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (15476)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (15486)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (15495)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (15491)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (15485)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (15470)Refutation not found, incomplete strategy% (15470)------------------------------
% 0.22/0.54  % (15470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15470)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15470)Memory used [KB]: 10618
% 0.22/0.54  % (15470)Time elapsed: 0.105 s
% 0.22/0.54  % (15470)------------------------------
% 0.22/0.54  % (15470)------------------------------
% 0.22/0.54  % (15475)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (15480)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (15485)Refutation not found, incomplete strategy% (15485)------------------------------
% 0.22/0.54  % (15485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15485)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15485)Memory used [KB]: 10618
% 0.22/0.54  % (15485)Time elapsed: 0.126 s
% 0.22/0.54  % (15485)------------------------------
% 0.22/0.54  % (15485)------------------------------
% 0.22/0.55  % (15477)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (15493)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (15487)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.55  % (15468)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.44/0.55  % (15497)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.56  % (15490)Refutation not found, incomplete strategy% (15490)------------------------------
% 1.44/0.56  % (15490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (15490)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (15490)Memory used [KB]: 10746
% 1.44/0.56  % (15490)Time elapsed: 0.115 s
% 1.44/0.56  % (15490)------------------------------
% 1.44/0.56  % (15490)------------------------------
% 1.44/0.56  % (15495)Refutation found. Thanks to Tanya!
% 1.44/0.56  % SZS status Theorem for theBenchmark
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f289,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(avatar_sat_refutation,[],[f83,f95,f97,f247,f288])).
% 1.44/0.56  fof(f288,plain,(
% 1.44/0.56    spl11_2 | ~spl11_4),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f287])).
% 1.44/0.56  fof(f287,plain,(
% 1.44/0.56    $false | (spl11_2 | ~spl11_4)),
% 1.44/0.56    inference(subsumption_resolution,[],[f286,f47])).
% 1.44/0.56  fof(f47,plain,(
% 1.44/0.56    v1_relat_1(sK3)),
% 1.44/0.56    inference(cnf_transformation,[],[f28])).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    (k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3)),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f27])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f14,plain,(
% 1.44/0.56    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f12])).
% 1.44/0.56  fof(f12,negated_conjecture,(
% 1.44/0.56    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.44/0.56    inference(negated_conjecture,[],[f11])).
% 1.44/0.56  fof(f11,conjecture,(
% 1.44/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.44/0.56  fof(f286,plain,(
% 1.44/0.56    ~v1_relat_1(sK3) | (spl11_2 | ~spl11_4)),
% 1.44/0.56    inference(subsumption_resolution,[],[f284,f91])).
% 1.44/0.56  fof(f91,plain,(
% 1.44/0.56    v1_relat_1(k1_xboole_0) | ~spl11_4),
% 1.44/0.56    inference(avatar_component_clause,[],[f89])).
% 1.44/0.56  fof(f89,plain,(
% 1.44/0.56    spl11_4 <=> v1_relat_1(k1_xboole_0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.44/0.56  fof(f284,plain,(
% 1.44/0.56    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK3) | (spl11_2 | ~spl11_4)),
% 1.44/0.56    inference(resolution,[],[f283,f68])).
% 1.44/0.56  fof(f68,plain,(
% 1.44/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f21])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(flattening,[],[f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,axiom,(
% 1.44/0.56    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.44/0.56  fof(f283,plain,(
% 1.44/0.56    ~v1_relat_1(k5_relat_1(sK3,k1_xboole_0)) | (spl11_2 | ~spl11_4)),
% 1.44/0.56    inference(subsumption_resolution,[],[f282,f47])).
% 1.44/0.56  fof(f282,plain,(
% 1.44/0.56    ~v1_relat_1(k5_relat_1(sK3,k1_xboole_0)) | ~v1_relat_1(sK3) | (spl11_2 | ~spl11_4)),
% 1.44/0.56    inference(subsumption_resolution,[],[f281,f91])).
% 1.44/0.56  fof(f281,plain,(
% 1.44/0.56    ~v1_relat_1(k5_relat_1(sK3,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK3) | (spl11_2 | ~spl11_4)),
% 1.44/0.56    inference(resolution,[],[f276,f140])).
% 1.44/0.56  fof(f140,plain,(
% 1.44/0.56    ( ! [X0,X1] : (sP1(X0,X1,k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f139,f68])).
% 1.44/0.56  fof(f139,plain,(
% 1.44/0.56    ( ! [X0,X1] : (sP1(X0,X1,k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(resolution,[],[f74,f62])).
% 1.44/0.56  fof(f62,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (sP2(X2,X1,X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f26])).
% 1.44/0.56  fof(f26,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (! [X2] : (sP2(X2,X1,X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(definition_folding,[],[f17,f25,f24,f23])).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    ! [X1,X4,X0,X3] : (sP0(X1,X4,X0,X3) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))),
% 1.44/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> sP0(X1,X4,X0,X3)))),
% 1.44/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    ! [X2,X1,X0] : ((k5_relat_1(X0,X1) = X2 <=> sP1(X0,X1,X2)) | ~sP2(X2,X1,X0))),
% 1.44/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.44/0.56  fof(f17,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f7])).
% 1.44/0.56  fof(f7,axiom,(
% 1.44/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 1.44/0.56  fof(f74,plain,(
% 1.44/0.56    ( ! [X2,X1] : (~sP2(k5_relat_1(X2,X1),X1,X2) | sP1(X2,X1,k5_relat_1(X2,X1))) )),
% 1.44/0.56    inference(equality_resolution,[],[f53])).
% 1.44/0.56  fof(f53,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | k5_relat_1(X2,X1) != X0 | ~sP2(X0,X1,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f32])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (((k5_relat_1(X2,X1) = X0 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k5_relat_1(X2,X1) != X0)) | ~sP2(X0,X1,X2))),
% 1.44/0.56    inference(rectify,[],[f31])).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ! [X2,X1,X0] : (((k5_relat_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k5_relat_1(X0,X1) != X2)) | ~sP2(X2,X1,X0))),
% 1.44/0.56    inference(nnf_transformation,[],[f25])).
% 1.44/0.56  fof(f276,plain,(
% 1.44/0.56    ( ! [X0] : (~sP1(sK3,k1_xboole_0,X0) | ~v1_relat_1(X0)) ) | (spl11_2 | ~spl11_4)),
% 1.44/0.56    inference(subsumption_resolution,[],[f275,f181])).
% 1.44/0.56  fof(f181,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~sP1(X0,k1_xboole_0,X1) | k1_xboole_0 = X1 | ~v1_relat_1(X1)) )),
% 1.44/0.56    inference(resolution,[],[f179,f52])).
% 1.44/0.56  fof(f52,plain,(
% 1.44/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f29])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f16,plain,(
% 1.44/0.56    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(flattening,[],[f15])).
% 1.44/0.56  fof(f15,plain,(
% 1.44/0.56    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,axiom,(
% 1.44/0.56    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 1.44/0.56  fof(f179,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~sP1(X3,k1_xboole_0,X2)) )),
% 1.44/0.56    inference(resolution,[],[f175,f55])).
% 1.44/0.56  fof(f55,plain,(
% 1.44/0.56    ( ! [X6,X2,X0,X5,X1] : (sP0(X1,X6,X0,X5) | ~r2_hidden(k4_tarski(X5,X6),X2) | ~sP1(X0,X1,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f36])).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK7(X0,X1,X2),X0,sK6(X0,X1,X2)) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & (sP0(X1,sK7(X0,X1,X2),X0,sK6(X0,X1,X2)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~sP0(X1,X6,X0,X5)) & (sP0(X1,X6,X0,X5) | ~r2_hidden(k4_tarski(X5,X6),X2))) | ~sP1(X0,X1,X2)))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f34,f35])).
% 1.44/0.56  fof(f35,plain,(
% 1.44/0.56    ! [X2,X1,X0] : (? [X3,X4] : ((~sP0(X1,X4,X0,X3) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (sP0(X1,X4,X0,X3) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~sP0(X1,sK7(X0,X1,X2),X0,sK6(X0,X1,X2)) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & (sP0(X1,sK7(X0,X1,X2),X0,sK6(X0,X1,X2)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2))))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f34,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3,X4] : ((~sP0(X1,X4,X0,X3) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (sP0(X1,X4,X0,X3) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~sP0(X1,X6,X0,X5)) & (sP0(X1,X6,X0,X5) | ~r2_hidden(k4_tarski(X5,X6),X2))) | ~sP1(X0,X1,X2)))),
% 1.44/0.56    inference(rectify,[],[f33])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3,X4] : ((~sP0(X1,X4,X0,X3) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (sP0(X1,X4,X0,X3) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~sP0(X1,X4,X0,X3)) & (sP0(X1,X4,X0,X3) | ~r2_hidden(k4_tarski(X3,X4),X2))) | ~sP1(X0,X1,X2)))),
% 1.44/0.56    inference(nnf_transformation,[],[f24])).
% 1.44/0.56  fof(f175,plain,(
% 1.44/0.56    ( ! [X6,X7,X5] : (~sP0(k1_xboole_0,X5,X6,X7)) )),
% 1.44/0.56    inference(resolution,[],[f60,f101])).
% 1.44/0.56  fof(f101,plain,(
% 1.44/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.44/0.56    inference(condensation,[],[f100])).
% 1.44/0.56  fof(f100,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.44/0.56    inference(resolution,[],[f66,f50])).
% 1.44/0.56  fof(f50,plain,(
% 1.44/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f5])).
% 1.44/0.56  fof(f5,axiom,(
% 1.44/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.44/0.56  fof(f66,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f42])).
% 1.44/0.56  fof(f42,plain,(
% 1.44/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f18,f41])).
% 1.44/0.56  fof(f41,plain,(
% 1.44/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f18,plain,(
% 1.44/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.44/0.56    inference(ennf_transformation,[],[f13])).
% 1.44/0.56  fof(f13,plain,(
% 1.44/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.44/0.56    inference(rectify,[],[f2])).
% 1.44/0.56  fof(f2,axiom,(
% 1.44/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.44/0.56  fof(f60,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X1),X0) | ~sP0(X0,X1,X2,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f40])).
% 1.44/0.56  fof(f40,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(k4_tarski(X3,X4),X2))) & ((r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X1),X0) & r2_hidden(k4_tarski(X3,sK8(X0,X1,X2,X3)),X2)) | ~sP0(X0,X1,X2,X3)))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f39])).
% 1.44/0.56  fof(f39,plain,(
% 1.44/0.56    ! [X3,X2,X1,X0] : (? [X5] : (r2_hidden(k4_tarski(X5,X1),X0) & r2_hidden(k4_tarski(X3,X5),X2)) => (r2_hidden(k4_tarski(sK8(X0,X1,X2,X3),X1),X0) & r2_hidden(k4_tarski(X3,sK8(X0,X1,X2,X3)),X2)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f38,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(k4_tarski(X3,X4),X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X1),X0) & r2_hidden(k4_tarski(X3,X5),X2)) | ~sP0(X0,X1,X2,X3)))),
% 1.44/0.56    inference(rectify,[],[f37])).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ! [X1,X4,X0,X3] : ((sP0(X1,X4,X0,X3) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~sP0(X1,X4,X0,X3)))),
% 1.44/0.56    inference(nnf_transformation,[],[f23])).
% 1.44/0.56  fof(f275,plain,(
% 1.44/0.56    ( ! [X0] : (~sP1(sK3,k1_xboole_0,X0) | k1_xboole_0 != X0 | ~v1_relat_1(X0)) ) | (spl11_2 | ~spl11_4)),
% 1.44/0.56    inference(subsumption_resolution,[],[f274,f47])).
% 1.44/0.56  fof(f274,plain,(
% 1.44/0.56    ( ! [X0] : (~sP1(sK3,k1_xboole_0,X0) | k1_xboole_0 != X0 | ~v1_relat_1(X0) | ~v1_relat_1(sK3)) ) | (spl11_2 | ~spl11_4)),
% 1.44/0.56    inference(subsumption_resolution,[],[f273,f91])).
% 1.44/0.56  fof(f273,plain,(
% 1.44/0.56    ( ! [X0] : (~sP1(sK3,k1_xboole_0,X0) | k1_xboole_0 != X0 | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK3)) ) | spl11_2),
% 1.44/0.56    inference(resolution,[],[f269,f62])).
% 1.44/0.56  fof(f269,plain,(
% 1.44/0.56    ( ! [X0] : (~sP2(X0,k1_xboole_0,sK3) | ~sP1(sK3,k1_xboole_0,X0) | k1_xboole_0 != X0) ) | spl11_2),
% 1.44/0.56    inference(superposition,[],[f82,f54])).
% 1.44/0.56  fof(f54,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (k5_relat_1(X2,X1) = X0 | ~sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f32])).
% 1.44/0.56  fof(f82,plain,(
% 1.44/0.56    k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | spl11_2),
% 1.44/0.56    inference(avatar_component_clause,[],[f80])).
% 1.44/0.56  fof(f80,plain,(
% 1.44/0.56    spl11_2 <=> k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.44/0.56  fof(f247,plain,(
% 1.44/0.56    spl11_1 | ~spl11_4),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f246])).
% 1.44/0.56  fof(f246,plain,(
% 1.44/0.56    $false | (spl11_1 | ~spl11_4)),
% 1.44/0.56    inference(subsumption_resolution,[],[f245,f91])).
% 1.44/0.56  fof(f245,plain,(
% 1.44/0.56    ~v1_relat_1(k1_xboole_0) | (spl11_1 | ~spl11_4)),
% 1.44/0.56    inference(subsumption_resolution,[],[f242,f47])).
% 1.44/0.56  fof(f242,plain,(
% 1.44/0.56    ~v1_relat_1(sK3) | ~v1_relat_1(k1_xboole_0) | (spl11_1 | ~spl11_4)),
% 1.44/0.56    inference(resolution,[],[f240,f68])).
% 1.44/0.56  fof(f240,plain,(
% 1.44/0.56    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK3)) | (spl11_1 | ~spl11_4)),
% 1.44/0.56    inference(subsumption_resolution,[],[f239,f47])).
% 1.44/0.56  fof(f239,plain,(
% 1.44/0.56    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK3)) | ~v1_relat_1(sK3) | (spl11_1 | ~spl11_4)),
% 1.44/0.56    inference(trivial_inequality_removal,[],[f232])).
% 1.44/0.56  fof(f232,plain,(
% 1.44/0.56    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK3)) | ~v1_relat_1(sK3) | (spl11_1 | ~spl11_4)),
% 1.44/0.56    inference(superposition,[],[f78,f173])).
% 1.44/0.56  fof(f173,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) ) | ~spl11_4),
% 1.44/0.56    inference(subsumption_resolution,[],[f172,f91])).
% 1.44/0.56  fof(f172,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.44/0.56    inference(resolution,[],[f169,f140])).
% 1.44/0.56  fof(f169,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~sP1(k1_xboole_0,X0,X1) | k1_xboole_0 = X1 | ~v1_relat_1(X1)) )),
% 1.44/0.56    inference(resolution,[],[f167,f52])).
% 1.44/0.56  fof(f167,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~sP1(k1_xboole_0,X3,X2)) )),
% 1.44/0.56    inference(resolution,[],[f163,f55])).
% 1.44/0.56  fof(f163,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~sP0(X0,X1,k1_xboole_0,X2)) )),
% 1.44/0.56    inference(resolution,[],[f59,f101])).
% 1.44/0.56  fof(f59,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK8(X0,X1,X2,X3)),X2) | ~sP0(X0,X1,X2,X3)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f40])).
% 1.44/0.56  fof(f78,plain,(
% 1.44/0.56    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) | spl11_1),
% 1.44/0.56    inference(avatar_component_clause,[],[f76])).
% 1.44/0.56  fof(f76,plain,(
% 1.44/0.56    spl11_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.44/0.56  fof(f97,plain,(
% 1.44/0.56    spl11_3 | spl11_4),
% 1.44/0.56    inference(avatar_split_clause,[],[f96,f89,f86])).
% 1.44/0.56  fof(f86,plain,(
% 1.44/0.56    spl11_3 <=> ! [X0] : ~v1_relat_1(X0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.44/0.56  fof(f96,plain,(
% 1.44/0.56    ( ! [X0] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(superposition,[],[f73,f72])).
% 1.44/0.56  fof(f72,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.44/0.56    inference(definition_unfolding,[],[f51,f63])).
% 1.44/0.56  fof(f63,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,axiom,(
% 1.44/0.56    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.44/0.56  fof(f51,plain,(
% 1.44/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f3])).
% 1.44/0.56  fof(f3,axiom,(
% 1.44/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.44/0.56  fof(f73,plain,(
% 1.44/0.56    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f67,f63])).
% 1.44/0.56  fof(f67,plain,(
% 1.44/0.56    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f19])).
% 1.44/0.56  fof(f19,plain,(
% 1.44/0.56    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f9])).
% 1.44/0.56  fof(f9,axiom,(
% 1.44/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.44/0.56  fof(f95,plain,(
% 1.44/0.56    ~spl11_3),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f93])).
% 1.44/0.56  fof(f93,plain,(
% 1.44/0.56    $false | ~spl11_3),
% 1.44/0.56    inference(subsumption_resolution,[],[f47,f87])).
% 1.44/0.56  fof(f87,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl11_3),
% 1.44/0.56    inference(avatar_component_clause,[],[f86])).
% 1.44/0.56  fof(f83,plain,(
% 1.44/0.56    ~spl11_1 | ~spl11_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f48,f80,f76])).
% 1.44/0.56  fof(f48,plain,(
% 1.44/0.56    k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)),
% 1.44/0.56    inference(cnf_transformation,[],[f28])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (15495)------------------------------
% 1.44/0.56  % (15495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (15495)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (15495)Memory used [KB]: 6396
% 1.44/0.56  % (15495)Time elapsed: 0.137 s
% 1.44/0.56  % (15495)------------------------------
% 1.44/0.56  % (15495)------------------------------
% 1.44/0.56  % (15467)Success in time 0.192 s
%------------------------------------------------------------------------------
