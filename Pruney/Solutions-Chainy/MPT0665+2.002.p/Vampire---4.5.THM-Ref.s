%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:17 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 120 expanded)
%              Number of leaves         :   17 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  294 ( 477 expanded)
%              Number of equality atoms :   25 (  27 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f818,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f812])).

fof(f812,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f811])).

fof(f811,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f810,f73])).

fof(f73,plain,
    ( r2_hidden(sK5,sK6)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl10_2
  <=> r2_hidden(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f810,plain,
    ( ~ r2_hidden(sK5,sK6)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f809,f201])).

fof(f201,plain,
    ( ! [X0,X1] : sP3(sK7,X0,X1)
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f88,f83,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X2,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP4(X2,X1,X0)
          & sP3(X0,X2,X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f11,f20,f19])).

fof(f19,plain,(
    ! [X0,X2,X1] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> r2_hidden(k4_tarski(X1,X2),X0) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> k1_xboole_0 = X2 )
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f83,plain,
    ( v1_funct_1(sK7)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl10_4
  <=> v1_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f88,plain,
    ( v1_relat_1(sK7)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl10_5
  <=> v1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f809,plain,
    ( ~ sP3(sK7,k1_funct_1(sK7,sK5),sK5)
    | ~ r2_hidden(sK5,sK6)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f787,f78])).

fof(f78,plain,
    ( r2_hidden(sK5,k1_relat_1(sK7))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl10_3
  <=> r2_hidden(sK5,k1_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f787,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK7))
    | ~ sP3(sK7,k1_funct_1(sK7,sK5),sK5)
    | ~ r2_hidden(sK5,sK6)
    | spl10_1
    | ~ spl10_5 ),
    inference(resolution,[],[f64,f682])).

fof(f682,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k4_tarski(X2,k1_funct_1(sK7,sK5)),sK7)
        | ~ r2_hidden(X2,sK6) )
    | spl10_1
    | ~ spl10_5 ),
    inference(resolution,[],[f673,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ r2_hidden(k4_tarski(X2,X1),X0)
      | ~ r2_hidden(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ~ r2_hidden(k4_tarski(X2,X1),X0)
        | ~ r2_hidden(X2,X3) )
      & ( ( r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(X2,X3) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X4,X3,X1] :
      ( ( sP0(X0,X4,X3,X1)
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | ~ r2_hidden(X3,X1) )
      & ( ( r2_hidden(k4_tarski(X3,X4),X0)
          & r2_hidden(X3,X1) )
        | ~ sP0(X0,X4,X3,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X4,X3,X1] :
      ( ( sP0(X0,X4,X3,X1)
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | ~ r2_hidden(X3,X1) )
      & ( ( r2_hidden(k4_tarski(X3,X4),X0)
          & r2_hidden(X3,X1) )
        | ~ sP0(X0,X4,X3,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X4,X3,X1] :
      ( sP0(X0,X4,X3,X1)
    <=> ( r2_hidden(k4_tarski(X3,X4),X0)
        & r2_hidden(X3,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f673,plain,
    ( ! [X0] : ~ sP0(sK7,k1_funct_1(sK7,sK5),X0,sK6)
    | spl10_1
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f206,f203,f45])).

fof(f45,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( ~ sP0(X1,X6,X5,X0)
      | r2_hidden(k4_tarski(X5,X6),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK9(X0,X1,X2),sK8(X0,X1,X2),X0)
            | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) )
          & ( sP0(X1,sK9(X0,X1,X2),sK8(X0,X1,X2),X0)
            | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ sP0(X1,X6,X5,X0) )
            & ( sP0(X1,X6,X5,X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ sP0(X1,X4,X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( sP0(X1,X4,X3,X0)
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ sP0(X1,sK9(X0,X1,X2),sK8(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) )
        & ( sP0(X1,sK9(X0,X1,X2),sK8(X0,X1,X2),X0)
          | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ sP0(X1,X4,X3,X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( sP0(X1,X4,X3,X0)
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ sP0(X1,X6,X5,X0) )
            & ( sP0(X1,X6,X5,X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3,X4] :
            ( ( ~ sP0(X0,X4,X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( sP0(X0,X4,X3,X1)
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X2)
              | ~ sP0(X0,X4,X3,X1) )
            & ( sP0(X0,X4,X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X2)
        <=> sP0(X0,X4,X3,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f203,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK7,sK5)),k7_relat_1(sK7,sK6))
    | spl10_1
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f90,f68,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f68,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),k2_relat_1(k7_relat_1(sK7,sK6)))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl10_1
  <=> r2_hidden(k1_funct_1(sK7,sK5),k2_relat_1(k7_relat_1(sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f90,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK7,X0))
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f88,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f206,plain,
    ( ! [X0] : sP1(X0,sK7,k7_relat_1(sK7,X0))
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f111,f61])).

fof(f61,plain,(
    ! [X2,X1] :
      ( ~ sP2(k7_relat_1(X1,X2),X1,X2)
      | sP1(X2,X1,k7_relat_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | k7_relat_1(X1,X2) != X0
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( k7_relat_1(X1,X2) = X0
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | k7_relat_1(X1,X2) != X0 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ( ( k7_relat_1(X0,X1) = X2
          | ~ sP1(X1,X0,X2) )
        & ( sP1(X1,X0,X2)
          | k7_relat_1(X0,X1) != X2 ) )
      | ~ sP2(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ( k7_relat_1(X0,X1) = X2
      <=> sP1(X1,X0,X2) )
      | ~ sP2(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f111,plain,
    ( ! [X0,X1] : sP2(k7_relat_1(sK7,X0),sK7,X1)
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f88,f90,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP2(X2,X0,X1)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f9,f17,f16,f15])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f64,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,k1_funct_1(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP3(X0,k1_funct_1(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,X1),X0)
      | k1_funct_1(X0,X2) != X1
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_funct_1(X0,X2) = X1
          | ~ r2_hidden(k4_tarski(X2,X1),X0) )
        & ( r2_hidden(k4_tarski(X2,X1),X0)
          | k1_funct_1(X0,X2) != X1 ) )
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ( ( k1_funct_1(X0,X1) = X2
          | ~ r2_hidden(k4_tarski(X1,X2),X0) )
        & ( r2_hidden(k4_tarski(X1,X2),X0)
          | k1_funct_1(X0,X1) != X2 ) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP3(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f89,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f37,f86])).

fof(f37,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),k2_relat_1(k7_relat_1(sK7,sK6)))
    & r2_hidden(sK5,sK6)
    & r2_hidden(sK5,k1_relat_1(sK7))
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f8,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
        & r2_hidden(X0,X1)
        & r2_hidden(X0,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK7,sK5),k2_relat_1(k7_relat_1(sK7,sK6)))
      & r2_hidden(sK5,sK6)
      & r2_hidden(sK5,k1_relat_1(sK7))
      & v1_funct_1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r2_hidden(X0,X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
         => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X0,X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
       => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

fof(f84,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f38,f81])).

fof(f38,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    r2_hidden(sK5,k1_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f41,f66])).

fof(f41,plain,(
    ~ r2_hidden(k1_funct_1(sK7,sK5),k2_relat_1(k7_relat_1(sK7,sK6))) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.42  % (1261)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.18/0.46  % (1261)Refutation found. Thanks to Tanya!
% 0.18/0.46  % SZS status Theorem for theBenchmark
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f818,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f812])).
% 0.18/0.46  fof(f812,plain,(
% 0.18/0.46    spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5),
% 0.18/0.46    inference(avatar_contradiction_clause,[],[f811])).
% 0.18/0.46  fof(f811,plain,(
% 0.18/0.46    $false | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5)),
% 0.18/0.46    inference(subsumption_resolution,[],[f810,f73])).
% 0.18/0.46  fof(f73,plain,(
% 0.18/0.46    r2_hidden(sK5,sK6) | ~spl10_2),
% 0.18/0.46    inference(avatar_component_clause,[],[f71])).
% 0.18/0.46  fof(f71,plain,(
% 0.18/0.46    spl10_2 <=> r2_hidden(sK5,sK6)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.18/0.46  fof(f810,plain,(
% 0.18/0.46    ~r2_hidden(sK5,sK6) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5)),
% 0.18/0.46    inference(subsumption_resolution,[],[f809,f201])).
% 0.18/0.46  fof(f201,plain,(
% 0.18/0.46    ( ! [X0,X1] : (sP3(sK7,X0,X1)) ) | (~spl10_4 | ~spl10_5)),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f88,f83,f56])).
% 0.18/0.46  fof(f56,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (sP3(X0,X2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f21])).
% 0.18/0.46  fof(f21,plain,(
% 0.18/0.46    ! [X0] : (! [X1,X2] : (sP4(X2,X1,X0) & sP3(X0,X2,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.46    inference(definition_folding,[],[f11,f20,f19])).
% 0.18/0.46  fof(f19,plain,(
% 0.18/0.46    ! [X0,X2,X1] : ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~sP3(X0,X2,X1))),
% 0.18/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.18/0.46  fof(f20,plain,(
% 0.18/0.46    ! [X2,X1,X0] : ((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0)) | ~sP4(X2,X1,X0))),
% 0.18/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.18/0.46  fof(f11,plain,(
% 0.18/0.46    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.46    inference(flattening,[],[f10])).
% 0.18/0.46  fof(f10,plain,(
% 0.18/0.46    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f4])).
% 0.18/0.46  fof(f4,axiom,(
% 0.18/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.18/0.46  fof(f83,plain,(
% 0.18/0.46    v1_funct_1(sK7) | ~spl10_4),
% 0.18/0.46    inference(avatar_component_clause,[],[f81])).
% 0.18/0.46  fof(f81,plain,(
% 0.18/0.46    spl10_4 <=> v1_funct_1(sK7)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.18/0.46  fof(f88,plain,(
% 0.18/0.46    v1_relat_1(sK7) | ~spl10_5),
% 0.18/0.46    inference(avatar_component_clause,[],[f86])).
% 0.18/0.46  fof(f86,plain,(
% 0.18/0.46    spl10_5 <=> v1_relat_1(sK7)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.18/0.46  fof(f809,plain,(
% 0.18/0.46    ~sP3(sK7,k1_funct_1(sK7,sK5),sK5) | ~r2_hidden(sK5,sK6) | (spl10_1 | ~spl10_3 | ~spl10_5)),
% 0.18/0.46    inference(subsumption_resolution,[],[f787,f78])).
% 0.18/0.46  fof(f78,plain,(
% 0.18/0.46    r2_hidden(sK5,k1_relat_1(sK7)) | ~spl10_3),
% 0.18/0.46    inference(avatar_component_clause,[],[f76])).
% 0.18/0.47  fof(f76,plain,(
% 0.18/0.47    spl10_3 <=> r2_hidden(sK5,k1_relat_1(sK7))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.18/0.47  fof(f787,plain,(
% 0.18/0.47    ~r2_hidden(sK5,k1_relat_1(sK7)) | ~sP3(sK7,k1_funct_1(sK7,sK5),sK5) | ~r2_hidden(sK5,sK6) | (spl10_1 | ~spl10_5)),
% 0.18/0.47    inference(resolution,[],[f64,f682])).
% 0.18/0.47  fof(f682,plain,(
% 0.18/0.47    ( ! [X2] : (~r2_hidden(k4_tarski(X2,k1_funct_1(sK7,sK5)),sK7) | ~r2_hidden(X2,sK6)) ) | (spl10_1 | ~spl10_5)),
% 0.18/0.47    inference(resolution,[],[f673,f50])).
% 0.18/0.47  fof(f50,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(X2,X3)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f32])).
% 0.18/0.47  fof(f32,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(X2,X3)) & ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(X2,X3)) | ~sP0(X0,X1,X2,X3)))),
% 0.18/0.47    inference(rectify,[],[f31])).
% 0.18/0.47  fof(f31,plain,(
% 0.18/0.47    ! [X0,X4,X3,X1] : ((sP0(X0,X4,X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~sP0(X0,X4,X3,X1)))),
% 0.18/0.47    inference(flattening,[],[f30])).
% 0.18/0.47  fof(f30,plain,(
% 0.18/0.47    ! [X0,X4,X3,X1] : ((sP0(X0,X4,X3,X1) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~sP0(X0,X4,X3,X1)))),
% 0.18/0.47    inference(nnf_transformation,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    ! [X0,X4,X3,X1] : (sP0(X0,X4,X3,X1) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))),
% 0.18/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.18/0.47  fof(f673,plain,(
% 0.18/0.47    ( ! [X0] : (~sP0(sK7,k1_funct_1(sK7,sK5),X0,sK6)) ) | (spl10_1 | ~spl10_5)),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f206,f203,f45])).
% 0.18/0.47  fof(f45,plain,(
% 0.18/0.47    ( ! [X6,X2,X0,X5,X1] : (~sP0(X1,X6,X5,X0) | r2_hidden(k4_tarski(X5,X6),X2) | ~sP1(X0,X1,X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f29])).
% 0.18/0.47  fof(f29,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK9(X0,X1,X2),sK8(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2)) & (sP0(X1,sK9(X0,X1,X2),sK8(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~sP0(X1,X6,X5,X0)) & (sP0(X1,X6,X5,X0) | ~r2_hidden(k4_tarski(X5,X6),X2))) | ~sP1(X0,X1,X2)))),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f27,f28])).
% 0.18/0.47  fof(f28,plain,(
% 0.18/0.47    ! [X2,X1,X0] : (? [X3,X4] : ((~sP0(X1,X4,X3,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (sP0(X1,X4,X3,X0) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~sP0(X1,sK9(X0,X1,X2),sK8(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2)) & (sP0(X1,sK9(X0,X1,X2),sK8(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2))))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f27,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3,X4] : ((~sP0(X1,X4,X3,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (sP0(X1,X4,X3,X0) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~sP0(X1,X6,X5,X0)) & (sP0(X1,X6,X5,X0) | ~r2_hidden(k4_tarski(X5,X6),X2))) | ~sP1(X0,X1,X2)))),
% 0.18/0.47    inference(rectify,[],[f26])).
% 0.18/0.47  fof(f26,plain,(
% 0.18/0.47    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3,X4] : ((~sP0(X0,X4,X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (sP0(X0,X4,X3,X1) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~sP0(X0,X4,X3,X1)) & (sP0(X0,X4,X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2))) | ~sP1(X1,X0,X2)))),
% 0.18/0.47    inference(nnf_transformation,[],[f16])).
% 0.18/0.47  fof(f16,plain,(
% 0.18/0.47    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> sP0(X0,X4,X3,X1)))),
% 0.18/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.18/0.47  fof(f203,plain,(
% 0.18/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(X0,k1_funct_1(sK7,sK5)),k7_relat_1(sK7,sK6))) ) | (spl10_1 | ~spl10_5)),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f90,f68,f60])).
% 0.18/0.47  fof(f60,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f14])).
% 0.18/0.47  fof(f14,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.18/0.47    inference(flattening,[],[f13])).
% 0.18/0.47  fof(f13,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.18/0.47    inference(ennf_transformation,[],[f3])).
% 0.18/0.47  fof(f3,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.18/0.47  fof(f68,plain,(
% 0.18/0.47    ~r2_hidden(k1_funct_1(sK7,sK5),k2_relat_1(k7_relat_1(sK7,sK6))) | spl10_1),
% 0.18/0.47    inference(avatar_component_clause,[],[f66])).
% 0.18/0.47  fof(f66,plain,(
% 0.18/0.47    spl10_1 <=> r2_hidden(k1_funct_1(sK7,sK5),k2_relat_1(k7_relat_1(sK7,sK6)))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.18/0.47  fof(f90,plain,(
% 0.18/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK7,X0))) ) | ~spl10_5),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f88,f58])).
% 0.18/0.47  fof(f58,plain,(
% 0.18/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f12])).
% 0.18/0.47  fof(f12,plain,(
% 0.18/0.47    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f2])).
% 0.18/0.47  fof(f2,axiom,(
% 0.18/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.18/0.47  fof(f206,plain,(
% 0.18/0.47    ( ! [X0] : (sP1(X0,sK7,k7_relat_1(sK7,X0))) ) | ~spl10_5),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f111,f61])).
% 0.18/0.47  fof(f61,plain,(
% 0.18/0.47    ( ! [X2,X1] : (~sP2(k7_relat_1(X1,X2),X1,X2) | sP1(X2,X1,k7_relat_1(X1,X2))) )),
% 0.18/0.47    inference(equality_resolution,[],[f42])).
% 0.18/0.47  fof(f42,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | k7_relat_1(X1,X2) != X0 | ~sP2(X0,X1,X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f25])).
% 0.18/0.47  fof(f25,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (((k7_relat_1(X1,X2) = X0 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k7_relat_1(X1,X2) != X0)) | ~sP2(X0,X1,X2))),
% 0.18/0.47    inference(rectify,[],[f24])).
% 0.18/0.47  fof(f24,plain,(
% 0.18/0.47    ! [X2,X0,X1] : (((k7_relat_1(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k7_relat_1(X0,X1) != X2)) | ~sP2(X2,X0,X1))),
% 0.18/0.47    inference(nnf_transformation,[],[f17])).
% 0.18/0.47  fof(f17,plain,(
% 0.18/0.47    ! [X2,X0,X1] : ((k7_relat_1(X0,X1) = X2 <=> sP1(X1,X0,X2)) | ~sP2(X2,X0,X1))),
% 0.18/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.18/0.47  fof(f111,plain,(
% 0.18/0.47    ( ! [X0,X1] : (sP2(k7_relat_1(sK7,X0),sK7,X1)) ) | ~spl10_5),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f88,f90,f51])).
% 0.18/0.47  fof(f51,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (sP2(X2,X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f18])).
% 0.18/0.47  fof(f18,plain,(
% 0.18/0.47    ! [X0] : (! [X1,X2] : (sP2(X2,X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.18/0.47    inference(definition_folding,[],[f9,f17,f16,f15])).
% 0.18/0.47  fof(f9,plain,(
% 0.18/0.47    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f1])).
% 0.18/0.47  fof(f1,axiom,(
% 0.18/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
% 0.18/0.47  fof(f64,plain,(
% 0.18/0.47    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,k1_funct_1(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0)) | ~sP3(X0,k1_funct_1(X0,X2),X2)) )),
% 0.18/0.47    inference(equality_resolution,[],[f54])).
% 0.18/0.47  fof(f54,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,X1),X0) | k1_funct_1(X0,X2) != X1 | ~r2_hidden(X2,k1_relat_1(X0)) | ~sP3(X0,X1,X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f36])).
% 0.18/0.47  fof(f36,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (((k1_funct_1(X0,X2) = X1 | ~r2_hidden(k4_tarski(X2,X1),X0)) & (r2_hidden(k4_tarski(X2,X1),X0) | k1_funct_1(X0,X2) != X1)) | ~r2_hidden(X2,k1_relat_1(X0)) | ~sP3(X0,X1,X2))),
% 0.18/0.47    inference(rectify,[],[f35])).
% 0.18/0.47  fof(f35,plain,(
% 0.18/0.47    ! [X0,X2,X1] : (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~sP3(X0,X2,X1))),
% 0.18/0.47    inference(nnf_transformation,[],[f19])).
% 0.18/0.47  fof(f89,plain,(
% 0.18/0.47    spl10_5),
% 0.18/0.47    inference(avatar_split_clause,[],[f37,f86])).
% 0.18/0.47  fof(f37,plain,(
% 0.18/0.47    v1_relat_1(sK7)),
% 0.18/0.47    inference(cnf_transformation,[],[f23])).
% 0.18/0.47  fof(f23,plain,(
% 0.18/0.47    ~r2_hidden(k1_funct_1(sK7,sK5),k2_relat_1(k7_relat_1(sK7,sK6))) & r2_hidden(sK5,sK6) & r2_hidden(sK5,k1_relat_1(sK7)) & v1_funct_1(sK7) & v1_relat_1(sK7)),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f8,f22])).
% 0.18/0.47  fof(f22,plain,(
% 0.18/0.47    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r2_hidden(k1_funct_1(sK7,sK5),k2_relat_1(k7_relat_1(sK7,sK6))) & r2_hidden(sK5,sK6) & r2_hidden(sK5,k1_relat_1(sK7)) & v1_funct_1(sK7) & v1_relat_1(sK7))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f8,plain,(
% 0.18/0.47    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.18/0.47    inference(flattening,[],[f7])).
% 0.18/0.47  fof(f7,plain,(
% 0.18/0.47    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & (r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.18/0.47    inference(ennf_transformation,[],[f6])).
% 0.18/0.47  fof(f6,negated_conjecture,(
% 0.18/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.18/0.47    inference(negated_conjecture,[],[f5])).
% 0.18/0.47  fof(f5,conjecture,(
% 0.18/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).
% 0.18/0.47  fof(f84,plain,(
% 0.18/0.47    spl10_4),
% 0.18/0.47    inference(avatar_split_clause,[],[f38,f81])).
% 0.18/0.47  fof(f38,plain,(
% 0.18/0.47    v1_funct_1(sK7)),
% 0.18/0.47    inference(cnf_transformation,[],[f23])).
% 0.18/0.47  fof(f79,plain,(
% 0.18/0.47    spl10_3),
% 0.18/0.47    inference(avatar_split_clause,[],[f39,f76])).
% 0.18/0.47  fof(f39,plain,(
% 0.18/0.47    r2_hidden(sK5,k1_relat_1(sK7))),
% 0.18/0.47    inference(cnf_transformation,[],[f23])).
% 0.18/0.47  fof(f74,plain,(
% 0.18/0.47    spl10_2),
% 0.18/0.47    inference(avatar_split_clause,[],[f40,f71])).
% 0.18/0.47  fof(f40,plain,(
% 0.18/0.47    r2_hidden(sK5,sK6)),
% 0.18/0.47    inference(cnf_transformation,[],[f23])).
% 0.18/0.47  fof(f69,plain,(
% 0.18/0.47    ~spl10_1),
% 0.18/0.47    inference(avatar_split_clause,[],[f41,f66])).
% 0.18/0.47  fof(f41,plain,(
% 0.18/0.47    ~r2_hidden(k1_funct_1(sK7,sK5),k2_relat_1(k7_relat_1(sK7,sK6)))),
% 0.18/0.47    inference(cnf_transformation,[],[f23])).
% 0.18/0.47  % SZS output end Proof for theBenchmark
% 0.18/0.47  % (1261)------------------------------
% 0.18/0.47  % (1261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (1261)Termination reason: Refutation
% 0.18/0.47  
% 0.18/0.47  % (1261)Memory used [KB]: 11897
% 0.18/0.47  % (1261)Time elapsed: 0.072 s
% 0.18/0.47  % (1261)------------------------------
% 0.18/0.47  % (1261)------------------------------
% 0.18/0.47  % (1244)Success in time 0.129 s
%------------------------------------------------------------------------------
