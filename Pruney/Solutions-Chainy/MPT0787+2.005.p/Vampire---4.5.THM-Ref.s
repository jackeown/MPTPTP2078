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
% DateTime   : Thu Dec  3 12:56:04 EST 2020

% Result     : Theorem 29.39s
% Output     : Refutation 29.39s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 848 expanded)
%              Number of leaves         :   33 ( 203 expanded)
%              Depth                    :   21
%              Number of atoms          :  944 (5011 expanded)
%              Number of equality atoms :  115 ( 394 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47331,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f131,f302,f315,f405,f413,f514,f524,f1046,f1058,f1615,f1631,f1647,f1890,f2936,f47312])).

fof(f47312,plain,
    ( ~ spl14_1
    | spl14_2
    | spl14_12
    | ~ spl14_23
    | ~ spl14_33 ),
    inference(avatar_contradiction_clause,[],[f47311])).

fof(f47311,plain,
    ( $false
    | ~ spl14_1
    | spl14_2
    | spl14_12
    | ~ spl14_23
    | ~ spl14_33 ),
    inference(subsumption_resolution,[],[f47310,f129])).

fof(f129,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl14_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl14_2
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f47310,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_1
    | spl14_2
    | spl14_12
    | ~ spl14_23
    | ~ spl14_33 ),
    inference(subsumption_resolution,[],[f47309,f235])).

fof(f235,plain,
    ( sK0 != sK1
    | spl14_12 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl14_12
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f47309,plain,
    ( sK0 = sK1
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_1
    | spl14_2
    | ~ spl14_23
    | ~ spl14_33 ),
    inference(subsumption_resolution,[],[f47287,f124])).

fof(f124,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl14_1
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f47287,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_1
    | spl14_2
    | ~ spl14_23
    | ~ spl14_33 ),
    inference(superposition,[],[f619,f47022])).

fof(f47022,plain,
    ( sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_1
    | spl14_2
    | ~ spl14_33 ),
    inference(subsumption_resolution,[],[f47021,f129])).

fof(f47021,plain,
    ( sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_1
    | ~ spl14_33 ),
    inference(duplicate_literal_removal,[],[f47017])).

fof(f47017,plain,
    ( sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_1
    | ~ spl14_33 ),
    inference(resolution,[],[f4397,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK13(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK13(X0,X1),X1)
          & r2_hidden(sK13(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f65,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK13(X0,X1),X1)
        & r2_hidden(sK13(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f4397,plain,
    ( ! [X8] :
        ( r2_hidden(sK13(k1_wellord1(sK2,sK0),X8),k1_wellord1(sK2,sK1))
        | sK1 = sK13(k1_wellord1(sK2,sK0),X8)
        | r1_tarski(k1_wellord1(sK2,sK0),X8) )
    | ~ spl14_1
    | ~ spl14_33 ),
    inference(resolution,[],[f2058,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | X0 = X1
      | r2_hidden(X0,k1_wellord1(sK2,X1)) ) ),
    inference(resolution,[],[f116,f68])).

fof(f68,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
      | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
      | r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
        | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
        | r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

fof(f116,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0)
                | sK10(X0,X1,X2) = X1
                | ~ r2_hidden(sK10(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0)
                  & sK10(X0,X1,X2) != X1 )
                | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0)
          | sK10(X0,X1,X2) = X1
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0)
            & sK10(X0,X1,X2) != X1 )
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f2058,plain,
    ( ! [X4] :
        ( r2_hidden(k4_tarski(sK13(k1_wellord1(sK2,sK0),X4),sK1),sK2)
        | r1_tarski(k1_wellord1(sK2,sK0),X4) )
    | ~ spl14_1
    | ~ spl14_33 ),
    inference(resolution,[],[f1917,f163])).

fof(f163,plain,(
    ! [X2,X1] :
      ( r2_hidden(k4_tarski(sK13(k1_wellord1(sK2,X1),X2),X1),sK2)
      | r1_tarski(k1_wellord1(sK2,X1),X2) ) ),
    inference(resolution,[],[f161,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK13(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
      | r2_hidden(k4_tarski(X0,X1),sK2) ) ),
    inference(resolution,[],[f117,f68])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1917,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK0),sK2)
        | r2_hidden(k4_tarski(X0,sK1),sK2) )
    | ~ spl14_1
    | ~ spl14_33 ),
    inference(resolution,[],[f124,f513])).

fof(f513,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) )
    | ~ spl14_33 ),
    inference(avatar_component_clause,[],[f512])).

fof(f512,plain,
    ( spl14_33
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_33])])).

fof(f619,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,sK13(k1_wellord1(sK2,X0),X1)),sK2)
        | sK13(k1_wellord1(sK2,X0),X1) = X0
        | r1_tarski(k1_wellord1(sK2,X0),X1) )
    | ~ spl14_23 ),
    inference(resolution,[],[f404,f163])).

fof(f404,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X1,X0),sK2) )
    | ~ spl14_23 ),
    inference(avatar_component_clause,[],[f403])).

fof(f403,plain,
    ( spl14_23
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X1,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_23])])).

fof(f2936,plain,
    ( ~ spl14_86
    | spl14_12
    | ~ spl14_1
    | ~ spl14_23 ),
    inference(avatar_split_clause,[],[f2927,f403,f123,f234,f1518])).

fof(f1518,plain,
    ( spl14_86
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_86])])).

fof(f2927,plain,
    ( sK0 = sK1
    | ~ r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl14_1
    | ~ spl14_23 ),
    inference(resolution,[],[f124,f404])).

fof(f1890,plain,
    ( ~ spl14_2
    | spl14_12
    | ~ spl14_86 ),
    inference(avatar_contradiction_clause,[],[f1889])).

fof(f1889,plain,
    ( $false
    | ~ spl14_2
    | spl14_12
    | ~ spl14_86 ),
    inference(subsumption_resolution,[],[f1887,f68])).

fof(f1887,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl14_2
    | spl14_12
    | ~ spl14_86 ),
    inference(resolution,[],[f1864,f119])).

fof(f119,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1864,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ spl14_2
    | spl14_12
    | ~ spl14_86 ),
    inference(resolution,[],[f1672,f1670])).

fof(f1670,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | spl14_12
    | ~ spl14_86 ),
    inference(subsumption_resolution,[],[f1665,f235])).

fof(f1665,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl14_86 ),
    inference(resolution,[],[f1520,f193])).

fof(f1520,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl14_86 ),
    inference(avatar_component_clause,[],[f1518])).

fof(f1672,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,sK0))
        | r2_hidden(X0,k1_wellord1(sK2,sK1)) )
    | ~ spl14_2 ),
    inference(resolution,[],[f128,f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f128,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f1647,plain,
    ( spl14_12
    | spl14_86
    | spl14_1
    | ~ spl14_47 ),
    inference(avatar_split_clause,[],[f1516,f1044,f123,f1518,f234])).

fof(f1044,plain,
    ( spl14_47
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_47])])).

fof(f1516,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | sK0 = sK1
    | spl14_1
    | ~ spl14_47 ),
    inference(subsumption_resolution,[],[f1515,f71])).

fof(f71,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f1515,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | sK0 = sK1
    | spl14_1
    | ~ spl14_47 ),
    inference(subsumption_resolution,[],[f1505,f70])).

fof(f70,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f1505,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | sK0 = sK1
    | spl14_1
    | ~ spl14_47 ),
    inference(resolution,[],[f1045,f125])).

fof(f125,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f1045,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 )
    | ~ spl14_47 ),
    inference(avatar_component_clause,[],[f1044])).

fof(f1631,plain,
    ( spl14_2
    | ~ spl14_12 ),
    inference(avatar_contradiction_clause,[],[f1630])).

fof(f1630,plain,
    ( $false
    | spl14_2
    | ~ spl14_12 ),
    inference(subsumption_resolution,[],[f1629,f120])).

fof(f120,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1629,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl14_2
    | ~ spl14_12 ),
    inference(forward_demodulation,[],[f129,f236])).

fof(f236,plain,
    ( sK0 = sK1
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f234])).

fof(f1615,plain,
    ( spl14_1
    | ~ spl14_12
    | ~ spl14_18 ),
    inference(avatar_contradiction_clause,[],[f1614])).

fof(f1614,plain,
    ( $false
    | spl14_1
    | ~ spl14_12
    | ~ spl14_18 ),
    inference(subsumption_resolution,[],[f1586,f319])).

fof(f319,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl14_18 ),
    inference(backward_demodulation,[],[f192,f301])).

fof(f301,plain,
    ( k1_xboole_0 = k1_wellord1(sK2,k3_relat_1(sK2))
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl14_18
  <=> k1_xboole_0 = k1_wellord1(sK2,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f192,plain,(
    ! [X0] : r1_tarski(k1_wellord1(sK2,k3_relat_1(sK2)),X0) ),
    inference(resolution,[],[f174,f120])).

fof(f174,plain,(
    ! [X10,X9] :
      ( ~ r1_tarski(k3_relat_1(sK2),X9)
      | r1_tarski(k1_wellord1(sK2,X9),X10) ) ),
    inference(resolution,[],[f169,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f169,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k3_relat_1(sK2))
      | r1_tarski(k1_wellord1(sK2,X2),X3) ) ),
    inference(subsumption_resolution,[],[f165,f68])).

fof(f165,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_wellord1(sK2,X2),X3)
      | r2_hidden(X2,k3_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f163,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f1586,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl14_1
    | ~ spl14_12 ),
    inference(backward_demodulation,[],[f1552,f1572])).

fof(f1572,plain,
    ( k1_xboole_0 = sK12(sK2,sK0)
    | spl14_1
    | ~ spl14_12 ),
    inference(resolution,[],[f1551,f1029])).

fof(f1029,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK12(sK2,X0))
      | k1_xboole_0 = sK12(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f1028,f158])).

fof(f158,plain,(
    ! [X0] : r1_tarski(sK12(sK2,X0),k3_relat_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X0] :
      ( r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))
      | r1_tarski(sK12(sK2,X0),k3_relat_1(sK2)) ) ),
    inference(resolution,[],[f155,f112])).

fof(f155,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK13(sK12(sK2,X0),X1),k3_relat_1(sK2))
      | r1_tarski(sK12(sK2,X0),X1) ) ),
    inference(resolution,[],[f154,f111])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK12(sK2,X1))
      | r2_hidden(X0,k3_relat_1(sK2)) ) ),
    inference(resolution,[],[f104,f68])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,sK12(X0,X1))
      | r2_hidden(X3,k3_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( ( r2_hidden(X3,sK12(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK12(X0,X1)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
     => ! [X3] :
          ( ( r2_hidden(X3,sK12(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK12(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).

fof(f1028,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK12(sK2,X0))
      | k1_xboole_0 = sK12(sK2,X0)
      | ~ r1_tarski(sK12(sK2,X0),k3_relat_1(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f1021])).

fof(f1021,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK12(sK2,X0))
      | k1_xboole_0 = sK12(sK2,X0)
      | ~ r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))
      | k1_xboole_0 = sK12(sK2,X0) ) ),
    inference(resolution,[],[f1018,f271])).

fof(f271,plain,(
    ! [X3] :
      ( r2_hidden(sK11(sK2,sK12(sK2,X3)),sK12(sK2,X3))
      | k1_xboole_0 = sK12(sK2,X3) ) ),
    inference(resolution,[],[f266,f158])).

fof(f266,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_relat_1(sK2))
      | k1_xboole_0 = X0
      | r2_hidden(sK11(sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f265,f68])).

fof(f265,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_relat_1(sK2))
      | k1_xboole_0 = X0
      | r2_hidden(sK11(sK2,X0),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f264,f69])).

fof(f69,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f264,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_relat_1(sK2))
      | k1_xboole_0 = X0
      | r2_hidden(sK11(sK2,X0),X0)
      | ~ v2_wellord1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f262,f95])).

fof(f95,plain,(
    ! [X0] :
      ( r2_wellord1(X0,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( r2_wellord1(X0,k3_relat_1(X0))
          | ~ v2_wellord1(X0) )
        & ( v2_wellord1(X0)
          | ~ r2_wellord1(X0,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).

fof(f262,plain,(
    ! [X0,X1] :
      ( ~ r2_wellord1(sK2,X1)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r2_hidden(sK11(sK2,X0),X0) ) ),
    inference(resolution,[],[f102,f68])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | r2_hidden(sK11(X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ! [X4] :
                ( r2_hidden(k4_tarski(sK11(X1,X2),X4),X1)
                | ~ r2_hidden(X4,X2) )
            & r2_hidden(sK11(X1,X2),X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f26,f56])).

fof(f56,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X2) )
          & r2_hidden(X3,X2) )
     => ( ! [X4] :
            ( r2_hidden(k4_tarski(sK11(X1,X2),X4),X1)
            | ~ r2_hidden(X4,X2) )
        & r2_hidden(sK11(X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,X0)
       => ! [X2] :
            ~ ( ! [X3] :
                  ~ ( ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) )
                    & r2_hidden(X3,X2) )
              & k1_xboole_0 != X2
              & r1_tarski(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord1)).

fof(f1018,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(sK11(sK2,X9),sK12(sK2,X10))
      | ~ r2_hidden(X10,X9)
      | k1_xboole_0 = X9
      | ~ r1_tarski(X9,k3_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f1013,f68])).

fof(f1013,plain,(
    ! [X10,X9] :
      ( ~ r1_tarski(X9,k3_relat_1(sK2))
      | ~ r2_hidden(X10,X9)
      | k1_xboole_0 = X9
      | ~ r2_hidden(sK11(sK2,X9),sK12(sK2,X10))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f1008,f105])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,sK12(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1008,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK11(sK2,X0),X1),sK2)
      | ~ r1_tarski(X0,k3_relat_1(sK2))
      | ~ r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1007,f68])).

fof(f1007,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK2))
      | ~ r2_hidden(X1,X0)
      | r2_hidden(k4_tarski(sK11(sK2,X0),X1),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1006,f69])).

fof(f1006,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK2))
      | ~ r2_hidden(X1,X0)
      | r2_hidden(k4_tarski(sK11(sK2,X0),X1),sK2)
      | ~ v2_wellord1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f909,f95])).

fof(f909,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_wellord1(sK2,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(sK11(sK2,X1),X0),sK2) ) ),
    inference(resolution,[],[f103,f68])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X4,X2)
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | r2_hidden(k4_tarski(sK11(X1,X2),X4),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1551,plain,
    ( r2_hidden(sK0,sK12(sK2,sK0))
    | spl14_1
    | ~ spl14_12 ),
    inference(backward_demodulation,[],[f421,f236])).

fof(f421,plain,
    ( r2_hidden(sK0,sK12(sK2,sK1))
    | spl14_1 ),
    inference(subsumption_resolution,[],[f415,f70])).

fof(f415,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | r2_hidden(sK0,sK12(sK2,sK1))
    | spl14_1 ),
    inference(resolution,[],[f344,f125])).

fof(f344,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(X0,k3_relat_1(sK2))
      | r2_hidden(X0,sK12(sK2,X1)) ) ),
    inference(resolution,[],[f106,f68])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | r2_hidden(X3,sK12(X0,X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1552,plain,
    ( ~ r1_tarski(sK12(sK2,sK0),sK0)
    | spl14_1
    | ~ spl14_12 ),
    inference(backward_demodulation,[],[f433,f236])).

fof(f433,plain,
    ( ~ r1_tarski(sK12(sK2,sK1),sK0)
    | spl14_1 ),
    inference(resolution,[],[f421,f113])).

fof(f1058,plain,(
    spl14_46 ),
    inference(avatar_contradiction_clause,[],[f1057])).

fof(f1057,plain,
    ( $false
    | spl14_46 ),
    inference(subsumption_resolution,[],[f1056,f68])).

fof(f1056,plain,
    ( ~ v1_relat_1(sK2)
    | spl14_46 ),
    inference(subsumption_resolution,[],[f1051,f69])).

fof(f1051,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl14_46 ),
    inference(resolution,[],[f1042,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f1042,plain,
    ( ~ v6_relat_2(sK2)
    | spl14_46 ),
    inference(avatar_component_clause,[],[f1040])).

fof(f1040,plain,
    ( spl14_46
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_46])])).

fof(f1046,plain,
    ( ~ spl14_46
    | spl14_47 ),
    inference(avatar_split_clause,[],[f1038,f1044,f1040])).

fof(f1038,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK2)
      | X0 = X1
      | ~ r2_hidden(X1,k3_relat_1(sK2))
      | ~ r2_hidden(X0,k3_relat_1(sK2))
      | ~ v6_relat_2(sK2)
      | r2_hidden(k4_tarski(X1,X0),sK2) ) ),
    inference(resolution,[],[f78,f68])).

fof(f78,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)
            & sK5(X0) != sK6(X0)
            & r2_hidden(sK6(X0),k3_relat_1(X0))
            & r2_hidden(sK5(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)
        & sK5(X0) != sK6(X0)
        & r2_hidden(sK6(X0),k3_relat_1(X0))
        & r2_hidden(sK5(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(f524,plain,(
    spl14_32 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | spl14_32 ),
    inference(subsumption_resolution,[],[f522,f68])).

fof(f522,plain,
    ( ~ v1_relat_1(sK2)
    | spl14_32 ),
    inference(subsumption_resolution,[],[f518,f69])).

fof(f518,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl14_32 ),
    inference(resolution,[],[f510,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f510,plain,
    ( ~ v8_relat_2(sK2)
    | spl14_32 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl14_32
  <=> v8_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).

fof(f514,plain,
    ( ~ spl14_32
    | spl14_33 ),
    inference(avatar_split_clause,[],[f506,f512,f508])).

fof(f506,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(k4_tarski(X2,X0),sK2)
      | ~ v8_relat_2(sK2)
      | r2_hidden(k4_tarski(X2,X1),sK2) ) ),
    inference(resolution,[],[f84,f68])).

fof(f84,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X6),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0)
            & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)
            & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0)
        & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)
        & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

fof(f413,plain,(
    spl14_22 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | spl14_22 ),
    inference(subsumption_resolution,[],[f411,f68])).

fof(f411,plain,
    ( ~ v1_relat_1(sK2)
    | spl14_22 ),
    inference(subsumption_resolution,[],[f408,f69])).

fof(f408,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl14_22 ),
    inference(resolution,[],[f401,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f401,plain,
    ( ~ v4_relat_2(sK2)
    | spl14_22 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl14_22
  <=> v4_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).

fof(f405,plain,
    ( ~ spl14_22
    | spl14_23 ),
    inference(avatar_split_clause,[],[f397,f403,f399])).

fof(f397,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(k4_tarski(X1,X0),sK2)
      | ~ v4_relat_2(sK2)
      | X0 = X1 ) ),
    inference(resolution,[],[f74,f68])).

fof(f74,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | X3 = X4 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK3(X0) != sK4(X0)
            & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK3(X0) != sK4(X0)
        & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | ~ r2_hidden(k4_tarski(X2,X1),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(f315,plain,(
    ~ spl14_17 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl14_17 ),
    inference(subsumption_resolution,[],[f313,f192])).

fof(f313,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,k3_relat_1(sK2)),sK11(sK2,k1_wellord1(sK2,k3_relat_1(sK2))))
    | ~ spl14_17 ),
    inference(resolution,[],[f297,f113])).

fof(f297,plain,
    ( r2_hidden(sK11(sK2,k1_wellord1(sK2,k3_relat_1(sK2))),k1_wellord1(sK2,k3_relat_1(sK2)))
    | ~ spl14_17 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl14_17
  <=> r2_hidden(sK11(sK2,k1_wellord1(sK2,k3_relat_1(sK2))),k1_wellord1(sK2,k3_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f302,plain,
    ( spl14_17
    | spl14_18 ),
    inference(avatar_split_clause,[],[f292,f299,f295])).

fof(f292,plain,
    ( k1_xboole_0 = k1_wellord1(sK2,k3_relat_1(sK2))
    | r2_hidden(sK11(sK2,k1_wellord1(sK2,k3_relat_1(sK2))),k1_wellord1(sK2,k3_relat_1(sK2))) ),
    inference(resolution,[],[f192,f266])).

fof(f131,plain,
    ( spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f72,f127,f123])).

fof(f72,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f130,plain,
    ( ~ spl14_1
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f73,f127,f123])).

fof(f73,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (32737)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (32752)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (32744)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (32753)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (32736)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (32745)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (32734)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (32732)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (32733)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (32742)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (32735)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (32758)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (32756)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (32749)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (32730)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.54  % (32738)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.54  % (32740)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.54  % (32759)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.54  % (32757)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.54  % (32750)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (32751)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (32754)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.55  % (32741)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (32731)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.55  % (32748)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.55  % (32743)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.55  % (32746)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (32747)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  % (32739)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.58/0.56  % (32755)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.58/0.56  % (32747)Refutation not found, incomplete strategy% (32747)------------------------------
% 1.58/0.56  % (32747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (32747)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (32747)Memory used [KB]: 10746
% 1.58/0.58  % (32747)Time elapsed: 0.158 s
% 1.58/0.58  % (32747)------------------------------
% 1.58/0.58  % (32747)------------------------------
% 2.50/0.73  % (32760)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.05/0.81  % (32735)Time limit reached!
% 3.05/0.81  % (32735)------------------------------
% 3.05/0.81  % (32735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.81  % (32735)Termination reason: Time limit
% 3.05/0.81  
% 3.05/0.81  % (32735)Memory used [KB]: 8315
% 3.05/0.81  % (32735)Time elapsed: 0.405 s
% 3.05/0.81  % (32735)------------------------------
% 3.05/0.81  % (32735)------------------------------
% 3.82/0.90  % (32740)Time limit reached!
% 3.82/0.90  % (32740)------------------------------
% 3.82/0.90  % (32740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.91  % (32740)Termination reason: Time limit
% 3.82/0.91  % (32740)Termination phase: Saturation
% 3.82/0.91  
% 3.82/0.91  % (32740)Memory used [KB]: 12920
% 3.82/0.91  % (32740)Time elapsed: 0.500 s
% 3.82/0.91  % (32740)------------------------------
% 3.82/0.91  % (32740)------------------------------
% 3.82/0.92  % (32742)Time limit reached!
% 3.82/0.92  % (32742)------------------------------
% 3.82/0.92  % (32742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.92  % (32742)Termination reason: Time limit
% 3.82/0.92  % (32742)Termination phase: Saturation
% 3.82/0.92  
% 3.82/0.92  % (32742)Memory used [KB]: 8699
% 3.82/0.92  % (32742)Time elapsed: 0.524 s
% 3.82/0.92  % (32742)------------------------------
% 3.82/0.92  % (32742)------------------------------
% 3.82/0.92  % (32731)Time limit reached!
% 3.82/0.92  % (32731)------------------------------
% 3.82/0.92  % (32731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.92  % (32731)Termination reason: Time limit
% 3.82/0.92  
% 3.82/0.92  % (32731)Memory used [KB]: 8699
% 3.82/0.92  % (32731)Time elapsed: 0.513 s
% 3.82/0.92  % (32731)------------------------------
% 3.82/0.92  % (32731)------------------------------
% 3.82/0.94  % (32730)Time limit reached!
% 3.82/0.94  % (32730)------------------------------
% 3.82/0.94  % (32730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.94  % (32730)Termination reason: Time limit
% 3.82/0.94  
% 3.82/0.94  % (32730)Memory used [KB]: 3709
% 3.82/0.94  % (32730)Time elapsed: 0.526 s
% 3.82/0.94  % (32730)------------------------------
% 3.82/0.94  % (32730)------------------------------
% 4.48/0.94  % (32761)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.73/1.00  % (32758)Time limit reached!
% 4.73/1.00  % (32758)------------------------------
% 4.73/1.00  % (32758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.73/1.00  % (32737)Time limit reached!
% 4.73/1.00  % (32737)------------------------------
% 4.73/1.00  % (32737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.73/1.01  % (32758)Termination reason: Time limit
% 4.73/1.01  % (32758)Termination phase: Saturation
% 4.73/1.01  
% 4.73/1.01  % (32758)Memory used [KB]: 7419
% 4.73/1.01  % (32758)Time elapsed: 0.600 s
% 4.73/1.01  % (32758)------------------------------
% 4.73/1.01  % (32758)------------------------------
% 4.73/1.01  % (32746)Time limit reached!
% 4.73/1.01  % (32746)------------------------------
% 4.73/1.01  % (32746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.73/1.01  % (32746)Termination reason: Time limit
% 4.73/1.01  
% 4.73/1.01  % (32746)Memory used [KB]: 15095
% 4.73/1.01  % (32746)Time elapsed: 0.609 s
% 4.73/1.01  % (32746)------------------------------
% 4.73/1.01  % (32746)------------------------------
% 4.73/1.01  % (32737)Termination reason: Time limit
% 4.73/1.01  % (32737)Termination phase: Saturation
% 4.73/1.01  
% 4.73/1.01  % (32737)Memory used [KB]: 9338
% 4.73/1.01  % (32737)Time elapsed: 0.600 s
% 4.73/1.01  % (32737)------------------------------
% 4.73/1.01  % (32737)------------------------------
% 5.12/1.04  % (32764)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.12/1.05  % (32763)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.51/1.07  % (32762)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.51/1.09  % (32765)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 6.00/1.13  % (32767)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.00/1.15  % (300)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.00/1.17  % (32766)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.33/1.23  % (32751)Time limit reached!
% 6.33/1.23  % (32751)------------------------------
% 6.33/1.23  % (32751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.33/1.23  % (32751)Termination reason: Time limit
% 6.33/1.23  
% 6.33/1.23  % (32751)Memory used [KB]: 3965
% 6.33/1.23  % (32751)Time elapsed: 0.828 s
% 6.33/1.23  % (32751)------------------------------
% 6.33/1.23  % (32751)------------------------------
% 7.78/1.36  % (32763)Time limit reached!
% 7.78/1.36  % (32763)------------------------------
% 7.78/1.36  % (32763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.78/1.36  % (32763)Termination reason: Time limit
% 7.78/1.36  
% 7.78/1.36  % (32763)Memory used [KB]: 6908
% 7.78/1.36  % (32763)Time elapsed: 0.417 s
% 7.78/1.36  % (32763)------------------------------
% 7.78/1.36  % (32763)------------------------------
% 7.78/1.37  % (301)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.78/1.37  % (32764)Time limit reached!
% 7.78/1.37  % (32764)------------------------------
% 7.78/1.37  % (32764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.78/1.37  % (32764)Termination reason: Time limit
% 7.78/1.37  % (32764)Termination phase: Saturation
% 7.78/1.37  
% 7.78/1.37  % (32764)Memory used [KB]: 13048
% 7.78/1.37  % (32764)Time elapsed: 0.400 s
% 7.78/1.37  % (32764)------------------------------
% 7.78/1.37  % (32764)------------------------------
% 8.33/1.42  % (32732)Time limit reached!
% 8.33/1.42  % (32732)------------------------------
% 8.33/1.42  % (32732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.33/1.42  % (32732)Termination reason: Time limit
% 8.33/1.42  
% 8.33/1.42  % (32732)Memory used [KB]: 15863
% 8.33/1.42  % (32732)Time elapsed: 1.016 s
% 8.33/1.42  % (32732)------------------------------
% 8.33/1.42  % (32732)------------------------------
% 8.67/1.52  % (303)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.67/1.53  % (302)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 9.17/1.56  % (304)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 10.06/1.65  % (32752)Time limit reached!
% 10.06/1.65  % (32752)------------------------------
% 10.06/1.65  % (32752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.06/1.65  % (32752)Termination reason: Time limit
% 10.06/1.65  
% 10.06/1.65  % (32752)Memory used [KB]: 17398
% 10.06/1.65  % (32752)Time elapsed: 1.203 s
% 10.06/1.65  % (32752)------------------------------
% 10.06/1.65  % (32752)------------------------------
% 10.06/1.66  % (32756)Time limit reached!
% 10.06/1.66  % (32756)------------------------------
% 10.06/1.66  % (32756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.06/1.66  % (32756)Termination reason: Time limit
% 10.06/1.66  
% 10.06/1.66  % (32756)Memory used [KB]: 14839
% 10.06/1.66  % (32756)Time elapsed: 1.257 s
% 10.06/1.66  % (32756)------------------------------
% 10.06/1.66  % (32756)------------------------------
% 10.32/1.70  % (32754)Time limit reached!
% 10.32/1.70  % (32754)------------------------------
% 10.32/1.70  % (32754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.32/1.70  % (32754)Termination reason: Time limit
% 10.32/1.70  % (32754)Termination phase: Saturation
% 10.32/1.70  
% 10.32/1.70  % (32754)Memory used [KB]: 16502
% 10.32/1.70  % (32754)Time elapsed: 1.300 s
% 10.32/1.70  % (32754)------------------------------
% 10.32/1.70  % (32754)------------------------------
% 10.32/1.72  % (32745)Time limit reached!
% 10.32/1.72  % (32745)------------------------------
% 10.32/1.72  % (32745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.32/1.72  % (32745)Termination reason: Time limit
% 10.32/1.72  % (32745)Termination phase: Saturation
% 10.32/1.72  
% 10.32/1.72  % (32745)Memory used [KB]: 14072
% 10.32/1.72  % (32745)Time elapsed: 1.300 s
% 10.32/1.72  % (32745)------------------------------
% 10.32/1.72  % (32745)------------------------------
% 11.13/1.77  % (305)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 11.13/1.81  % (307)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.57/1.84  % (308)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.57/1.85  % (309)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.73/1.90  % (32734)Time limit reached!
% 11.73/1.90  % (32734)------------------------------
% 11.73/1.90  % (32734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.73/1.90  % (32734)Termination reason: Time limit
% 11.73/1.90  % (32734)Termination phase: Saturation
% 11.73/1.90  
% 11.73/1.90  % (32734)Memory used [KB]: 12537
% 11.73/1.90  % (32734)Time elapsed: 1.500 s
% 11.73/1.90  % (32734)------------------------------
% 11.73/1.90  % (32734)------------------------------
% 11.73/1.91  % (32757)Time limit reached!
% 11.73/1.91  % (32757)------------------------------
% 11.73/1.91  % (32757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.73/1.91  % (32757)Termination reason: Time limit
% 11.73/1.91  
% 11.73/1.91  % (32757)Memory used [KB]: 13432
% 11.73/1.91  % (32757)Time elapsed: 1.509 s
% 11.73/1.91  % (32757)------------------------------
% 11.73/1.91  % (32757)------------------------------
% 12.23/1.95  % (304)Time limit reached!
% 12.23/1.95  % (304)------------------------------
% 12.23/1.95  % (304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.23/1.95  % (304)Termination reason: Time limit
% 12.23/1.95  
% 12.23/1.95  % (304)Memory used [KB]: 2814
% 12.23/1.95  % (304)Time elapsed: 0.505 s
% 12.23/1.95  % (304)------------------------------
% 12.23/1.95  % (304)------------------------------
% 12.41/2.03  % (32741)Time limit reached!
% 12.41/2.03  % (32741)------------------------------
% 12.41/2.03  % (32741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.41/2.03  % (32741)Termination reason: Time limit
% 12.41/2.03  
% 12.41/2.03  % (32741)Memory used [KB]: 16758
% 12.41/2.03  % (32741)Time elapsed: 1.631 s
% 12.41/2.03  % (32741)------------------------------
% 12.41/2.03  % (32741)------------------------------
% 12.88/2.04  % (311)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.88/2.05  % (310)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 12.88/2.06  % (312)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.50/2.15  % (309)Time limit reached!
% 13.50/2.15  % (309)------------------------------
% 13.50/2.15  % (309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.50/2.15  % (309)Termination reason: Time limit
% 13.50/2.15  % (309)Termination phase: Saturation
% 13.50/2.15  
% 13.50/2.15  % (309)Memory used [KB]: 3837
% 13.50/2.15  % (309)Time elapsed: 0.400 s
% 13.50/2.15  % (309)------------------------------
% 13.50/2.15  % (309)------------------------------
% 13.50/2.16  % (313)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 14.80/2.25  % (32766)Time limit reached!
% 14.80/2.25  % (32766)------------------------------
% 14.80/2.25  % (32766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.80/2.25  % (32766)Termination reason: Time limit
% 14.80/2.25  
% 14.80/2.25  % (32766)Memory used [KB]: 7419
% 14.80/2.25  % (32766)Time elapsed: 1.214 s
% 14.80/2.25  % (32766)------------------------------
% 14.80/2.25  % (32766)------------------------------
% 14.80/2.27  % (32744)Time limit reached!
% 14.80/2.27  % (32744)------------------------------
% 14.80/2.27  % (32744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.80/2.27  % (314)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.09/2.28  % (32744)Termination reason: Time limit
% 15.09/2.28  
% 15.09/2.28  % (32744)Memory used [KB]: 4477
% 15.09/2.28  % (32744)Time elapsed: 1.816 s
% 15.09/2.28  % (32744)------------------------------
% 15.09/2.28  % (32744)------------------------------
% 15.75/2.38  % (315)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.75/2.39  % (312)Time limit reached!
% 15.75/2.39  % (312)------------------------------
% 15.75/2.39  % (312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.75/2.39  % (312)Termination reason: Time limit
% 15.75/2.39  
% 15.75/2.39  % (312)Memory used [KB]: 2302
% 15.75/2.39  % (312)Time elapsed: 0.422 s
% 15.75/2.39  % (312)------------------------------
% 15.75/2.39  % (312)------------------------------
% 15.75/2.40  % (316)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 16.27/2.45  % (32748)Time limit reached!
% 16.27/2.45  % (32748)------------------------------
% 16.27/2.45  % (32748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.55/2.46  % (32748)Termination reason: Time limit
% 16.55/2.46  
% 16.55/2.46  % (32748)Memory used [KB]: 14456
% 16.55/2.46  % (32748)Time elapsed: 2.038 s
% 16.55/2.46  % (32748)------------------------------
% 16.55/2.46  % (32748)------------------------------
% 16.55/2.49  % (32736)Time limit reached!
% 16.55/2.49  % (32736)------------------------------
% 16.55/2.49  % (32736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.55/2.49  % (32736)Termination reason: Time limit
% 16.55/2.49  % (32736)Termination phase: Saturation
% 16.55/2.49  
% 16.55/2.49  % (32736)Memory used [KB]: 15735
% 16.55/2.49  % (32736)Time elapsed: 2.0000 s
% 16.55/2.49  % (32736)------------------------------
% 16.55/2.49  % (32736)------------------------------
% 17.08/2.56  % (317)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.33/2.58  % (318)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 17.33/2.62  % (319)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.70/2.66  % (32762)Time limit reached!
% 17.70/2.66  % (32762)------------------------------
% 17.70/2.66  % (32762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.88/2.67  % (32762)Termination reason: Time limit
% 17.88/2.67  % (32762)Termination phase: Saturation
% 17.88/2.67  
% 17.88/2.67  % (32762)Memory used [KB]: 16886
% 17.88/2.67  % (32762)Time elapsed: 1.700 s
% 17.88/2.67  % (32762)------------------------------
% 17.88/2.67  % (32762)------------------------------
% 18.79/2.74  % (300)Time limit reached!
% 18.79/2.74  % (300)------------------------------
% 18.79/2.74  % (300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.79/2.74  % (300)Termination reason: Time limit
% 18.79/2.74  % (300)Termination phase: Saturation
% 18.79/2.74  
% 18.79/2.74  % (300)Memory used [KB]: 8827
% 18.79/2.74  % (300)Time elapsed: 1.700 s
% 18.79/2.74  % (300)------------------------------
% 18.79/2.74  % (300)------------------------------
% 19.16/2.82  % (320)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 19.16/2.84  % (317)Time limit reached!
% 19.16/2.84  % (317)------------------------------
% 19.16/2.84  % (317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.76/2.85  % (317)Termination reason: Time limit
% 19.76/2.85  
% 19.76/2.85  % (317)Memory used [KB]: 9722
% 19.76/2.85  % (317)Time elapsed: 0.414 s
% 19.76/2.85  % (317)------------------------------
% 19.76/2.85  % (317)------------------------------
% 19.97/2.92  % (319)Time limit reached!
% 19.97/2.92  % (319)------------------------------
% 19.97/2.92  % (319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.97/2.92  % (319)Termination reason: Time limit
% 19.97/2.92  
% 19.97/2.92  % (319)Memory used [KB]: 8827
% 19.97/2.92  % (319)Time elapsed: 0.412 s
% 19.97/2.92  % (319)------------------------------
% 19.97/2.92  % (319)------------------------------
% 20.56/2.95  % (308)Time limit reached!
% 20.56/2.95  % (308)------------------------------
% 20.56/2.95  % (308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.56/2.95  % (308)Termination reason: Time limit
% 20.56/2.95  
% 20.56/2.95  % (308)Memory used [KB]: 15607
% 20.56/2.95  % (308)Time elapsed: 1.228 s
% 20.56/2.95  % (308)------------------------------
% 20.56/2.95  % (308)------------------------------
% 20.56/2.95  % (32738)Time limit reached!
% 20.56/2.95  % (32738)------------------------------
% 20.56/2.95  % (32738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.56/2.95  % (32738)Termination reason: Time limit
% 20.56/2.95  
% 20.56/2.95  % (32738)Memory used [KB]: 22387
% 20.56/2.95  % (32738)Time elapsed: 2.530 s
% 20.56/2.95  % (32738)------------------------------
% 20.56/2.95  % (32738)------------------------------
% 21.18/3.03  % (32749)Time limit reached!
% 21.18/3.03  % (32749)------------------------------
% 21.18/3.03  % (32749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.18/3.03  % (32749)Termination reason: Time limit
% 21.18/3.03  
% 21.18/3.03  % (32749)Memory used [KB]: 23155
% 21.18/3.03  % (32749)Time elapsed: 2.622 s
% 21.18/3.03  % (32749)------------------------------
% 21.18/3.03  % (32749)------------------------------
% 22.79/3.25  % (311)Time limit reached!
% 22.79/3.25  % (311)------------------------------
% 22.79/3.25  % (311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.05/3.26  % (311)Termination reason: Time limit
% 23.05/3.26  % (311)Termination phase: Saturation
% 23.05/3.26  
% 23.05/3.26  % (311)Memory used [KB]: 9338
% 23.05/3.26  % (311)Time elapsed: 1.300 s
% 23.05/3.26  % (311)------------------------------
% 23.05/3.26  % (311)------------------------------
% 24.07/3.40  % (32743)Time limit reached!
% 24.07/3.40  % (32743)------------------------------
% 24.07/3.40  % (32743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.07/3.40  % (32743)Termination reason: Time limit
% 24.07/3.40  % (32743)Termination phase: Saturation
% 24.07/3.40  
% 24.07/3.40  % (32743)Memory used [KB]: 15351
% 24.07/3.40  % (32743)Time elapsed: 3.0000 s
% 24.07/3.40  % (32743)------------------------------
% 24.07/3.40  % (32743)------------------------------
% 26.05/3.67  % (32761)Time limit reached!
% 26.05/3.67  % (32761)------------------------------
% 26.05/3.67  % (32761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.05/3.67  % (32761)Termination reason: Time limit
% 26.05/3.67  
% 26.05/3.67  % (32761)Memory used [KB]: 15095
% 26.05/3.67  % (32761)Time elapsed: 2.821 s
% 26.05/3.67  % (32761)------------------------------
% 26.05/3.67  % (32761)------------------------------
% 29.39/4.07  % (32733)Refutation found. Thanks to Tanya!
% 29.39/4.07  % SZS status Theorem for theBenchmark
% 29.39/4.07  % SZS output start Proof for theBenchmark
% 29.39/4.07  fof(f47331,plain,(
% 29.39/4.07    $false),
% 29.39/4.07    inference(avatar_sat_refutation,[],[f130,f131,f302,f315,f405,f413,f514,f524,f1046,f1058,f1615,f1631,f1647,f1890,f2936,f47312])).
% 29.39/4.09  fof(f47312,plain,(
% 29.39/4.09    ~spl14_1 | spl14_2 | spl14_12 | ~spl14_23 | ~spl14_33),
% 29.39/4.09    inference(avatar_contradiction_clause,[],[f47311])).
% 29.39/4.09  fof(f47311,plain,(
% 29.39/4.09    $false | (~spl14_1 | spl14_2 | spl14_12 | ~spl14_23 | ~spl14_33)),
% 29.39/4.09    inference(subsumption_resolution,[],[f47310,f129])).
% 29.39/4.09  fof(f129,plain,(
% 29.39/4.09    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl14_2),
% 29.39/4.09    inference(avatar_component_clause,[],[f127])).
% 29.39/4.09  fof(f127,plain,(
% 29.39/4.09    spl14_2 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 29.39/4.09    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 29.39/4.09  fof(f47310,plain,(
% 29.39/4.09    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl14_1 | spl14_2 | spl14_12 | ~spl14_23 | ~spl14_33)),
% 29.39/4.09    inference(subsumption_resolution,[],[f47309,f235])).
% 29.39/4.09  fof(f235,plain,(
% 29.39/4.09    sK0 != sK1 | spl14_12),
% 29.39/4.09    inference(avatar_component_clause,[],[f234])).
% 29.39/4.09  fof(f234,plain,(
% 29.39/4.09    spl14_12 <=> sK0 = sK1),
% 29.39/4.09    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).
% 29.39/4.09  fof(f47309,plain,(
% 29.39/4.09    sK0 = sK1 | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl14_1 | spl14_2 | ~spl14_23 | ~spl14_33)),
% 29.39/4.09    inference(subsumption_resolution,[],[f47287,f124])).
% 29.39/4.09  fof(f124,plain,(
% 29.39/4.09    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl14_1),
% 29.39/4.09    inference(avatar_component_clause,[],[f123])).
% 29.39/4.09  fof(f123,plain,(
% 29.39/4.09    spl14_1 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 29.39/4.09    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 29.39/4.09  fof(f47287,plain,(
% 29.39/4.09    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1 | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl14_1 | spl14_2 | ~spl14_23 | ~spl14_33)),
% 29.39/4.09    inference(superposition,[],[f619,f47022])).
% 29.39/4.09  fof(f47022,plain,(
% 29.39/4.09    sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl14_1 | spl14_2 | ~spl14_33)),
% 29.39/4.09    inference(subsumption_resolution,[],[f47021,f129])).
% 29.39/4.09  fof(f47021,plain,(
% 29.39/4.09    sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl14_1 | ~spl14_33)),
% 29.39/4.09    inference(duplicate_literal_removal,[],[f47017])).
% 29.39/4.09  fof(f47017,plain,(
% 29.39/4.09    sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl14_1 | ~spl14_33)),
% 29.39/4.09    inference(resolution,[],[f4397,f112])).
% 29.39/4.09  fof(f112,plain,(
% 29.39/4.09    ( ! [X0,X1] : (~r2_hidden(sK13(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 29.39/4.09    inference(cnf_transformation,[],[f67])).
% 29.39/4.09  fof(f67,plain,(
% 29.39/4.09    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK13(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 29.39/4.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f65,f66])).
% 29.39/4.09  fof(f66,plain,(
% 29.39/4.09    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK13(X0,X1),X0)))),
% 29.39/4.09    introduced(choice_axiom,[])).
% 29.39/4.09  fof(f65,plain,(
% 29.39/4.09    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 29.39/4.09    inference(rectify,[],[f64])).
% 29.39/4.09  fof(f64,plain,(
% 29.39/4.09    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 29.39/4.09    inference(nnf_transformation,[],[f28])).
% 29.39/4.09  fof(f28,plain,(
% 29.39/4.09    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 29.39/4.09    inference(ennf_transformation,[],[f1])).
% 29.39/4.09  fof(f1,axiom,(
% 29.39/4.09    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 29.39/4.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 29.39/4.09  fof(f4397,plain,(
% 29.39/4.09    ( ! [X8] : (r2_hidden(sK13(k1_wellord1(sK2,sK0),X8),k1_wellord1(sK2,sK1)) | sK1 = sK13(k1_wellord1(sK2,sK0),X8) | r1_tarski(k1_wellord1(sK2,sK0),X8)) ) | (~spl14_1 | ~spl14_33)),
% 29.39/4.09    inference(resolution,[],[f2058,f193])).
% 29.39/4.09  fof(f193,plain,(
% 29.39/4.09    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | r2_hidden(X0,k1_wellord1(sK2,X1))) )),
% 29.39/4.09    inference(resolution,[],[f116,f68])).
% 29.39/4.09  fof(f68,plain,(
% 29.39/4.09    v1_relat_1(sK2)),
% 29.39/4.09    inference(cnf_transformation,[],[f35])).
% 29.39/4.09  fof(f35,plain,(
% 29.39/4.09    (~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2)),
% 29.39/4.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f34])).
% 29.39/4.09  fof(f34,plain,(
% 29.39/4.09    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2))),
% 29.39/4.09    introduced(choice_axiom,[])).
% 29.39/4.09  fof(f33,plain,(
% 29.39/4.09    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 29.39/4.09    inference(flattening,[],[f32])).
% 29.39/4.09  fof(f32,plain,(
% 29.39/4.09    ? [X0,X1,X2] : (((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 29.39/4.09    inference(nnf_transformation,[],[f16])).
% 29.39/4.09  fof(f16,plain,(
% 29.39/4.09    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 29.39/4.09    inference(flattening,[],[f15])).
% 29.39/4.09  fof(f15,plain,(
% 29.39/4.09    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 29.39/4.09    inference(ennf_transformation,[],[f14])).
% 29.39/4.09  fof(f14,negated_conjecture,(
% 29.39/4.09    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 29.39/4.09    inference(negated_conjecture,[],[f13])).
% 29.39/4.09  fof(f13,conjecture,(
% 29.39/4.09    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 29.39/4.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).
% 29.39/4.09  fof(f116,plain,(
% 29.39/4.09    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | r2_hidden(X4,k1_wellord1(X0,X1))) )),
% 29.39/4.09    inference(equality_resolution,[],[f98])).
% 29.39/4.09  fof(f98,plain,(
% 29.39/4.09    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 29.39/4.09    inference(cnf_transformation,[],[f55])).
% 29.39/4.09  fof(f55,plain,(
% 29.39/4.09    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0) | sK10(X0,X1,X2) = X1 | ~r2_hidden(sK10(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0) & sK10(X0,X1,X2) != X1) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 29.39/4.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f53,f54])).
% 29.39/4.09  fof(f54,plain,(
% 29.39/4.09    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0) | sK10(X0,X1,X2) = X1 | ~r2_hidden(sK10(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0) & sK10(X0,X1,X2) != X1) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 29.39/4.09    introduced(choice_axiom,[])).
% 29.39/4.09  fof(f53,plain,(
% 29.39/4.09    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 29.39/4.09    inference(rectify,[],[f52])).
% 29.39/4.09  fof(f52,plain,(
% 29.39/4.09    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 29.39/4.09    inference(flattening,[],[f51])).
% 29.39/4.09  fof(f51,plain,(
% 29.39/4.09    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 29.39/4.09    inference(nnf_transformation,[],[f24])).
% 29.39/4.09  fof(f24,plain,(
% 29.39/4.09    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 29.39/4.09    inference(ennf_transformation,[],[f5])).
% 29.39/4.09  fof(f5,axiom,(
% 29.39/4.09    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 29.39/4.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 29.39/4.09  fof(f2058,plain,(
% 29.39/4.09    ( ! [X4] : (r2_hidden(k4_tarski(sK13(k1_wellord1(sK2,sK0),X4),sK1),sK2) | r1_tarski(k1_wellord1(sK2,sK0),X4)) ) | (~spl14_1 | ~spl14_33)),
% 29.39/4.09    inference(resolution,[],[f1917,f163])).
% 29.39/4.09  fof(f163,plain,(
% 29.39/4.09    ( ! [X2,X1] : (r2_hidden(k4_tarski(sK13(k1_wellord1(sK2,X1),X2),X1),sK2) | r1_tarski(k1_wellord1(sK2,X1),X2)) )),
% 29.39/4.09    inference(resolution,[],[f161,f111])).
% 29.39/4.09  fof(f111,plain,(
% 29.39/4.09    ( ! [X0,X1] : (r2_hidden(sK13(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 29.39/4.09    inference(cnf_transformation,[],[f67])).
% 29.39/4.09  fof(f161,plain,(
% 29.39/4.09    ( ! [X0,X1] : (~r2_hidden(X0,k1_wellord1(sK2,X1)) | r2_hidden(k4_tarski(X0,X1),sK2)) )),
% 29.39/4.09    inference(resolution,[],[f117,f68])).
% 29.39/4.09  fof(f117,plain,(
% 29.39/4.09    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X4,X1),X0)) )),
% 29.39/4.09    inference(equality_resolution,[],[f97])).
% 29.39/4.09  fof(f97,plain,(
% 29.39/4.09    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 29.39/4.09    inference(cnf_transformation,[],[f55])).
% 29.39/4.09  fof(f1917,plain,(
% 29.39/4.09    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK0),sK2) | r2_hidden(k4_tarski(X0,sK1),sK2)) ) | (~spl14_1 | ~spl14_33)),
% 29.39/4.09    inference(resolution,[],[f124,f513])).
% 29.39/4.09  fof(f513,plain,(
% 29.39/4.09    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X2,X1),sK2) | ~r2_hidden(k4_tarski(X2,X0),sK2)) ) | ~spl14_33),
% 29.39/4.09    inference(avatar_component_clause,[],[f512])).
% 29.39/4.09  fof(f512,plain,(
% 29.39/4.09    spl14_33 <=> ! [X1,X0,X2] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X2,X1),sK2) | ~r2_hidden(k4_tarski(X2,X0),sK2))),
% 29.39/4.09    introduced(avatar_definition,[new_symbols(naming,[spl14_33])])).
% 29.39/4.09  fof(f619,plain,(
% 29.39/4.09    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK13(k1_wellord1(sK2,X0),X1)),sK2) | sK13(k1_wellord1(sK2,X0),X1) = X0 | r1_tarski(k1_wellord1(sK2,X0),X1)) ) | ~spl14_23),
% 29.39/4.09    inference(resolution,[],[f404,f163])).
% 29.39/4.09  fof(f404,plain,(
% 29.39/4.09    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(k4_tarski(X1,X0),sK2)) ) | ~spl14_23),
% 29.39/4.09    inference(avatar_component_clause,[],[f403])).
% 29.39/4.09  fof(f403,plain,(
% 29.39/4.09    spl14_23 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(k4_tarski(X1,X0),sK2))),
% 29.39/4.09    introduced(avatar_definition,[new_symbols(naming,[spl14_23])])).
% 29.39/4.09  fof(f2936,plain,(
% 29.39/4.09    ~spl14_86 | spl14_12 | ~spl14_1 | ~spl14_23),
% 29.39/4.09    inference(avatar_split_clause,[],[f2927,f403,f123,f234,f1518])).
% 29.39/4.09  fof(f1518,plain,(
% 29.39/4.09    spl14_86 <=> r2_hidden(k4_tarski(sK1,sK0),sK2)),
% 29.39/4.09    introduced(avatar_definition,[new_symbols(naming,[spl14_86])])).
% 29.39/4.09  fof(f2927,plain,(
% 29.39/4.09    sK0 = sK1 | ~r2_hidden(k4_tarski(sK1,sK0),sK2) | (~spl14_1 | ~spl14_23)),
% 29.39/4.09    inference(resolution,[],[f124,f404])).
% 29.39/4.09  fof(f1890,plain,(
% 29.39/4.09    ~spl14_2 | spl14_12 | ~spl14_86),
% 29.39/4.09    inference(avatar_contradiction_clause,[],[f1889])).
% 29.39/4.09  fof(f1889,plain,(
% 29.39/4.09    $false | (~spl14_2 | spl14_12 | ~spl14_86)),
% 29.39/4.09    inference(subsumption_resolution,[],[f1887,f68])).
% 29.39/4.09  fof(f1887,plain,(
% 29.39/4.09    ~v1_relat_1(sK2) | (~spl14_2 | spl14_12 | ~spl14_86)),
% 29.39/4.09    inference(resolution,[],[f1864,f119])).
% 29.39/4.09  fof(f119,plain,(
% 29.39/4.09    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 29.39/4.09    inference(equality_resolution,[],[f118])).
% 29.39/4.09  fof(f118,plain,(
% 29.39/4.09    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 29.39/4.09    inference(equality_resolution,[],[f96])).
% 29.39/4.09  fof(f96,plain,(
% 29.39/4.09    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 29.39/4.09    inference(cnf_transformation,[],[f55])).
% 29.39/4.09  fof(f1864,plain,(
% 29.39/4.09    r2_hidden(sK1,k1_wellord1(sK2,sK1)) | (~spl14_2 | spl14_12 | ~spl14_86)),
% 29.39/4.09    inference(resolution,[],[f1672,f1670])).
% 29.39/4.09  fof(f1670,plain,(
% 29.39/4.09    r2_hidden(sK1,k1_wellord1(sK2,sK0)) | (spl14_12 | ~spl14_86)),
% 29.39/4.09    inference(subsumption_resolution,[],[f1665,f235])).
% 29.39/4.09  fof(f1665,plain,(
% 29.39/4.09    sK0 = sK1 | r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~spl14_86),
% 29.39/4.09    inference(resolution,[],[f1520,f193])).
% 29.39/4.09  fof(f1520,plain,(
% 29.39/4.09    r2_hidden(k4_tarski(sK1,sK0),sK2) | ~spl14_86),
% 29.39/4.09    inference(avatar_component_clause,[],[f1518])).
% 29.39/4.09  fof(f1672,plain,(
% 29.39/4.09    ( ! [X0] : (~r2_hidden(X0,k1_wellord1(sK2,sK0)) | r2_hidden(X0,k1_wellord1(sK2,sK1))) ) | ~spl14_2),
% 29.39/4.09    inference(resolution,[],[f128,f110])).
% 29.39/4.09  fof(f110,plain,(
% 29.39/4.09    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 29.39/4.09    inference(cnf_transformation,[],[f67])).
% 29.39/4.09  fof(f128,plain,(
% 29.39/4.09    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl14_2),
% 29.39/4.09    inference(avatar_component_clause,[],[f127])).
% 29.39/4.09  fof(f1647,plain,(
% 29.39/4.09    spl14_12 | spl14_86 | spl14_1 | ~spl14_47),
% 29.39/4.09    inference(avatar_split_clause,[],[f1516,f1044,f123,f1518,f234])).
% 29.39/4.09  fof(f1044,plain,(
% 29.39/4.09    spl14_47 <=> ! [X1,X0] : (r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1)),
% 29.39/4.09    introduced(avatar_definition,[new_symbols(naming,[spl14_47])])).
% 29.39/4.09  fof(f1516,plain,(
% 29.39/4.09    r2_hidden(k4_tarski(sK1,sK0),sK2) | sK0 = sK1 | (spl14_1 | ~spl14_47)),
% 29.39/4.09    inference(subsumption_resolution,[],[f1515,f71])).
% 29.39/4.09  fof(f71,plain,(
% 29.39/4.09    r2_hidden(sK1,k3_relat_1(sK2))),
% 29.39/4.09    inference(cnf_transformation,[],[f35])).
% 29.39/4.09  fof(f1515,plain,(
% 29.39/4.09    r2_hidden(k4_tarski(sK1,sK0),sK2) | ~r2_hidden(sK1,k3_relat_1(sK2)) | sK0 = sK1 | (spl14_1 | ~spl14_47)),
% 29.39/4.09    inference(subsumption_resolution,[],[f1505,f70])).
% 29.39/4.09  fof(f70,plain,(
% 29.39/4.09    r2_hidden(sK0,k3_relat_1(sK2))),
% 29.39/4.09    inference(cnf_transformation,[],[f35])).
% 29.39/4.09  fof(f1505,plain,(
% 29.39/4.09    r2_hidden(k4_tarski(sK1,sK0),sK2) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k3_relat_1(sK2)) | sK0 = sK1 | (spl14_1 | ~spl14_47)),
% 29.39/4.09    inference(resolution,[],[f1045,f125])).
% 29.39/4.09  fof(f125,plain,(
% 29.39/4.09    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | spl14_1),
% 29.39/4.09    inference(avatar_component_clause,[],[f123])).
% 29.39/4.09  fof(f1045,plain,(
% 29.39/4.09    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1) ) | ~spl14_47),
% 29.39/4.09    inference(avatar_component_clause,[],[f1044])).
% 29.39/4.09  fof(f1631,plain,(
% 29.39/4.09    spl14_2 | ~spl14_12),
% 29.39/4.09    inference(avatar_contradiction_clause,[],[f1630])).
% 29.39/4.09  fof(f1630,plain,(
% 29.39/4.09    $false | (spl14_2 | ~spl14_12)),
% 29.39/4.09    inference(subsumption_resolution,[],[f1629,f120])).
% 29.39/4.09  fof(f120,plain,(
% 29.39/4.09    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 29.39/4.09    inference(equality_resolution,[],[f108])).
% 29.39/4.09  fof(f108,plain,(
% 29.39/4.09    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 29.39/4.09    inference(cnf_transformation,[],[f63])).
% 29.39/4.09  fof(f63,plain,(
% 29.39/4.09    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 29.39/4.09    inference(flattening,[],[f62])).
% 29.39/4.09  fof(f62,plain,(
% 29.39/4.09    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 29.39/4.09    inference(nnf_transformation,[],[f2])).
% 29.39/4.09  fof(f2,axiom,(
% 29.39/4.09    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 29.39/4.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 29.39/4.09  fof(f1629,plain,(
% 29.39/4.09    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | (spl14_2 | ~spl14_12)),
% 29.39/4.09    inference(forward_demodulation,[],[f129,f236])).
% 29.39/4.09  fof(f236,plain,(
% 29.39/4.09    sK0 = sK1 | ~spl14_12),
% 29.39/4.09    inference(avatar_component_clause,[],[f234])).
% 29.39/4.09  fof(f1615,plain,(
% 29.39/4.09    spl14_1 | ~spl14_12 | ~spl14_18),
% 29.39/4.09    inference(avatar_contradiction_clause,[],[f1614])).
% 29.39/4.09  fof(f1614,plain,(
% 29.39/4.09    $false | (spl14_1 | ~spl14_12 | ~spl14_18)),
% 29.39/4.09    inference(subsumption_resolution,[],[f1586,f319])).
% 29.39/4.09  fof(f319,plain,(
% 29.39/4.09    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl14_18),
% 29.39/4.09    inference(backward_demodulation,[],[f192,f301])).
% 29.39/4.09  fof(f301,plain,(
% 29.39/4.09    k1_xboole_0 = k1_wellord1(sK2,k3_relat_1(sK2)) | ~spl14_18),
% 29.39/4.09    inference(avatar_component_clause,[],[f299])).
% 29.39/4.09  fof(f299,plain,(
% 29.39/4.09    spl14_18 <=> k1_xboole_0 = k1_wellord1(sK2,k3_relat_1(sK2))),
% 29.39/4.09    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).
% 29.39/4.09  fof(f192,plain,(
% 29.39/4.09    ( ! [X0] : (r1_tarski(k1_wellord1(sK2,k3_relat_1(sK2)),X0)) )),
% 29.39/4.09    inference(resolution,[],[f174,f120])).
% 29.39/4.09  fof(f174,plain,(
% 29.39/4.09    ( ! [X10,X9] : (~r1_tarski(k3_relat_1(sK2),X9) | r1_tarski(k1_wellord1(sK2,X9),X10)) )),
% 29.39/4.09    inference(resolution,[],[f169,f113])).
% 29.39/4.09  fof(f113,plain,(
% 29.39/4.09    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 29.39/4.09    inference(cnf_transformation,[],[f29])).
% 29.39/4.09  fof(f29,plain,(
% 29.39/4.09    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 29.39/4.09    inference(ennf_transformation,[],[f4])).
% 29.39/4.09  fof(f4,axiom,(
% 29.39/4.09    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 29.39/4.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 29.39/4.09  fof(f169,plain,(
% 29.39/4.09    ( ! [X2,X3] : (r2_hidden(X2,k3_relat_1(sK2)) | r1_tarski(k1_wellord1(sK2,X2),X3)) )),
% 29.39/4.09    inference(subsumption_resolution,[],[f165,f68])).
% 29.39/4.09  fof(f165,plain,(
% 29.39/4.09    ( ! [X2,X3] : (r1_tarski(k1_wellord1(sK2,X2),X3) | r2_hidden(X2,k3_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 29.39/4.09    inference(resolution,[],[f163,f115])).
% 29.39/4.09  fof(f115,plain,(
% 29.39/4.09    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 29.39/4.09    inference(cnf_transformation,[],[f31])).
% 29.39/4.09  fof(f31,plain,(
% 29.39/4.09    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 29.39/4.09    inference(flattening,[],[f30])).
% 29.39/4.09  fof(f30,plain,(
% 29.39/4.09    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 29.39/4.09    inference(ennf_transformation,[],[f3])).
% 29.39/4.09  fof(f3,axiom,(
% 29.39/4.09    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 29.39/4.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 29.39/4.09  fof(f1586,plain,(
% 29.39/4.09    ~r1_tarski(k1_xboole_0,sK0) | (spl14_1 | ~spl14_12)),
% 29.39/4.09    inference(backward_demodulation,[],[f1552,f1572])).
% 29.39/4.09  fof(f1572,plain,(
% 29.39/4.09    k1_xboole_0 = sK12(sK2,sK0) | (spl14_1 | ~spl14_12)),
% 29.39/4.09    inference(resolution,[],[f1551,f1029])).
% 29.39/4.09  fof(f1029,plain,(
% 29.39/4.09    ( ! [X0] : (~r2_hidden(X0,sK12(sK2,X0)) | k1_xboole_0 = sK12(sK2,X0)) )),
% 29.39/4.09    inference(subsumption_resolution,[],[f1028,f158])).
% 29.39/4.09  fof(f158,plain,(
% 29.39/4.09    ( ! [X0] : (r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))) )),
% 29.39/4.09    inference(duplicate_literal_removal,[],[f156])).
% 29.39/4.09  fof(f156,plain,(
% 29.39/4.09    ( ! [X0] : (r1_tarski(sK12(sK2,X0),k3_relat_1(sK2)) | r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))) )),
% 29.39/4.09    inference(resolution,[],[f155,f112])).
% 29.39/4.09  fof(f155,plain,(
% 29.39/4.09    ( ! [X0,X1] : (r2_hidden(sK13(sK12(sK2,X0),X1),k3_relat_1(sK2)) | r1_tarski(sK12(sK2,X0),X1)) )),
% 29.39/4.09    inference(resolution,[],[f154,f111])).
% 29.39/4.09  fof(f154,plain,(
% 29.39/4.09    ( ! [X0,X1] : (~r2_hidden(X0,sK12(sK2,X1)) | r2_hidden(X0,k3_relat_1(sK2))) )),
% 29.39/4.09    inference(resolution,[],[f104,f68])).
% 29.39/4.09  fof(f104,plain,(
% 29.39/4.09    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(X3,sK12(X0,X1)) | r2_hidden(X3,k3_relat_1(X0))) )),
% 29.39/4.09    inference(cnf_transformation,[],[f61])).
% 29.39/4.09  fof(f61,plain,(
% 29.39/4.09    ! [X0,X1] : (! [X3] : ((r2_hidden(X3,sK12(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,sK12(X0,X1)))) | ~v1_relat_1(X0))),
% 29.39/4.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f59,f60])).
% 29.39/4.09  fof(f60,plain,(
% 29.39/4.09    ! [X1,X0] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) => ! [X3] : ((r2_hidden(X3,sK12(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,sK12(X0,X1)))))),
% 29.39/4.09    introduced(choice_axiom,[])).
% 29.39/4.09  fof(f59,plain,(
% 29.39/4.09    ! [X0,X1] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~v1_relat_1(X0))),
% 29.39/4.09    inference(flattening,[],[f58])).
% 29.39/4.09  fof(f58,plain,(
% 29.39/4.09    ! [X0,X1] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0)))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~v1_relat_1(X0))),
% 29.39/4.09    inference(nnf_transformation,[],[f27])).
% 29.39/4.09  fof(f27,plain,(
% 29.39/4.09    ! [X0,X1] : (? [X2] : ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 29.39/4.09    inference(ennf_transformation,[],[f10])).
% 29.39/4.09  fof(f10,axiom,(
% 29.39/4.09    ! [X0,X1] : (v1_relat_1(X0) => ? [X2] : ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0)))))),
% 29.39/4.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).
% 29.39/4.09  fof(f1028,plain,(
% 29.39/4.09    ( ! [X0] : (~r2_hidden(X0,sK12(sK2,X0)) | k1_xboole_0 = sK12(sK2,X0) | ~r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))) )),
% 29.39/4.09    inference(duplicate_literal_removal,[],[f1021])).
% 29.39/4.09  fof(f1021,plain,(
% 29.39/4.09    ( ! [X0] : (~r2_hidden(X0,sK12(sK2,X0)) | k1_xboole_0 = sK12(sK2,X0) | ~r1_tarski(sK12(sK2,X0),k3_relat_1(sK2)) | k1_xboole_0 = sK12(sK2,X0)) )),
% 29.39/4.09    inference(resolution,[],[f1018,f271])).
% 29.39/4.09  fof(f271,plain,(
% 29.39/4.09    ( ! [X3] : (r2_hidden(sK11(sK2,sK12(sK2,X3)),sK12(sK2,X3)) | k1_xboole_0 = sK12(sK2,X3)) )),
% 29.39/4.09    inference(resolution,[],[f266,f158])).
% 29.39/4.09  fof(f266,plain,(
% 29.39/4.09    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK2)) | k1_xboole_0 = X0 | r2_hidden(sK11(sK2,X0),X0)) )),
% 29.39/4.09    inference(subsumption_resolution,[],[f265,f68])).
% 29.39/4.09  fof(f265,plain,(
% 29.39/4.09    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK2)) | k1_xboole_0 = X0 | r2_hidden(sK11(sK2,X0),X0) | ~v1_relat_1(sK2)) )),
% 29.39/4.09    inference(subsumption_resolution,[],[f264,f69])).
% 29.39/4.09  fof(f69,plain,(
% 29.39/4.09    v2_wellord1(sK2)),
% 29.39/4.09    inference(cnf_transformation,[],[f35])).
% 29.39/4.09  fof(f264,plain,(
% 29.39/4.09    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK2)) | k1_xboole_0 = X0 | r2_hidden(sK11(sK2,X0),X0) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2)) )),
% 29.39/4.09    inference(resolution,[],[f262,f95])).
% 29.39/4.09  fof(f95,plain,(
% 29.39/4.09    ( ! [X0] : (r2_wellord1(X0,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 29.39/4.09    inference(cnf_transformation,[],[f50])).
% 29.39/4.09  fof(f50,plain,(
% 29.39/4.09    ! [X0] : (((r2_wellord1(X0,k3_relat_1(X0)) | ~v2_wellord1(X0)) & (v2_wellord1(X0) | ~r2_wellord1(X0,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 29.39/4.09    inference(nnf_transformation,[],[f23])).
% 29.39/4.09  fof(f23,plain,(
% 29.39/4.09    ! [X0] : ((r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 29.39/4.09    inference(ennf_transformation,[],[f11])).
% 29.39/4.09  fof(f11,axiom,(
% 29.39/4.09    ! [X0] : (v1_relat_1(X0) => (r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)))),
% 29.39/4.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).
% 29.39/4.09  fof(f262,plain,(
% 29.39/4.09    ( ! [X0,X1] : (~r2_wellord1(sK2,X1) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r2_hidden(sK11(sK2,X0),X0)) )),
% 29.39/4.09    inference(resolution,[],[f102,f68])).
% 29.39/4.09  fof(f102,plain,(
% 29.39/4.09    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0) | ~r2_wellord1(X1,X0) | r2_hidden(sK11(X1,X2),X2)) )),
% 29.39/4.09    inference(cnf_transformation,[],[f57])).
% 29.39/4.09  fof(f57,plain,(
% 29.39/4.09    ! [X0,X1] : (! [X2] : ((! [X4] : (r2_hidden(k4_tarski(sK11(X1,X2),X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(sK11(X1,X2),X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0)) | ~r2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 29.39/4.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f26,f56])).
% 29.39/4.09  fof(f56,plain,(
% 29.39/4.09    ! [X2,X1] : (? [X3] : (! [X4] : (r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(X3,X2)) => (! [X4] : (r2_hidden(k4_tarski(sK11(X1,X2),X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(sK11(X1,X2),X2)))),
% 29.39/4.09    introduced(choice_axiom,[])).
% 29.39/4.09  fof(f26,plain,(
% 29.39/4.09    ! [X0,X1] : (! [X2] : (? [X3] : (! [X4] : (r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(X3,X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0)) | ~r2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 29.39/4.09    inference(flattening,[],[f25])).
% 29.39/4.09  fof(f25,plain,(
% 29.39/4.09    ! [X0,X1] : ((! [X2] : (? [X3] : (! [X4] : (r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(X3,X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0)) | ~r2_wellord1(X1,X0)) | ~v1_relat_1(X1))),
% 29.39/4.09    inference(ennf_transformation,[],[f12])).
% 29.39/4.09  fof(f12,axiom,(
% 29.39/4.09    ! [X0,X1] : (v1_relat_1(X1) => (r2_wellord1(X1,X0) => ! [X2] : ~(! [X3] : ~(! [X4] : (r2_hidden(X4,X2) => r2_hidden(k4_tarski(X3,X4),X1)) & r2_hidden(X3,X2)) & k1_xboole_0 != X2 & r1_tarski(X2,X0))))),
% 29.39/4.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord1)).
% 29.39/4.09  fof(f1018,plain,(
% 29.39/4.09    ( ! [X10,X9] : (~r2_hidden(sK11(sK2,X9),sK12(sK2,X10)) | ~r2_hidden(X10,X9) | k1_xboole_0 = X9 | ~r1_tarski(X9,k3_relat_1(sK2))) )),
% 29.39/4.09    inference(subsumption_resolution,[],[f1013,f68])).
% 29.39/4.09  fof(f1013,plain,(
% 29.39/4.09    ( ! [X10,X9] : (~r1_tarski(X9,k3_relat_1(sK2)) | ~r2_hidden(X10,X9) | k1_xboole_0 = X9 | ~r2_hidden(sK11(sK2,X9),sK12(sK2,X10)) | ~v1_relat_1(sK2)) )),
% 29.39/4.09    inference(resolution,[],[f1008,f105])).
% 29.39/4.09  fof(f105,plain,(
% 29.39/4.09    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,sK12(X0,X1)) | ~v1_relat_1(X0)) )),
% 29.39/4.09    inference(cnf_transformation,[],[f61])).
% 29.39/4.09  fof(f1008,plain,(
% 29.39/4.09    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK11(sK2,X0),X1),sK2) | ~r1_tarski(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,X0) | k1_xboole_0 = X0) )),
% 29.39/4.09    inference(subsumption_resolution,[],[f1007,f68])).
% 29.39/4.09  fof(f1007,plain,(
% 29.39/4.09    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,X0) | r2_hidden(k4_tarski(sK11(sK2,X0),X1),sK2) | ~v1_relat_1(sK2)) )),
% 29.39/4.09    inference(subsumption_resolution,[],[f1006,f69])).
% 29.39/4.09  fof(f1006,plain,(
% 29.39/4.09    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,X0) | r2_hidden(k4_tarski(sK11(sK2,X0),X1),sK2) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2)) )),
% 29.39/4.09    inference(resolution,[],[f909,f95])).
% 29.39/4.09  fof(f909,plain,(
% 29.39/4.09    ( ! [X2,X0,X1] : (~r2_wellord1(sK2,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK11(sK2,X1),X0),sK2)) )),
% 29.39/4.09    inference(resolution,[],[f103,f68])).
% 29.39/4.09  fof(f103,plain,(
% 29.39/4.09    ( ! [X4,X2,X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X4,X2) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0) | ~r2_wellord1(X1,X0) | r2_hidden(k4_tarski(sK11(X1,X2),X4),X1)) )),
% 29.39/4.09    inference(cnf_transformation,[],[f57])).
% 29.39/4.09  fof(f1551,plain,(
% 29.39/4.09    r2_hidden(sK0,sK12(sK2,sK0)) | (spl14_1 | ~spl14_12)),
% 29.39/4.09    inference(backward_demodulation,[],[f421,f236])).
% 29.39/4.09  fof(f421,plain,(
% 29.39/4.09    r2_hidden(sK0,sK12(sK2,sK1)) | spl14_1),
% 29.39/4.09    inference(subsumption_resolution,[],[f415,f70])).
% 29.39/4.09  fof(f415,plain,(
% 29.39/4.09    ~r2_hidden(sK0,k3_relat_1(sK2)) | r2_hidden(sK0,sK12(sK2,sK1)) | spl14_1),
% 29.39/4.09    inference(resolution,[],[f344,f125])).
% 29.39/4.09  fof(f344,plain,(
% 29.39/4.09    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(X0,sK12(sK2,X1))) )),
% 29.39/4.09    inference(resolution,[],[f106,f68])).
% 29.39/4.09  fof(f106,plain,(
% 29.39/4.09    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0)) | r2_hidden(X3,sK12(X0,X1))) )),
% 29.39/4.09    inference(cnf_transformation,[],[f61])).
% 29.39/4.09  fof(f1552,plain,(
% 29.39/4.09    ~r1_tarski(sK12(sK2,sK0),sK0) | (spl14_1 | ~spl14_12)),
% 29.39/4.09    inference(backward_demodulation,[],[f433,f236])).
% 29.39/4.09  fof(f433,plain,(
% 29.39/4.09    ~r1_tarski(sK12(sK2,sK1),sK0) | spl14_1),
% 29.39/4.09    inference(resolution,[],[f421,f113])).
% 29.39/4.09  fof(f1058,plain,(
% 29.39/4.09    spl14_46),
% 29.39/4.09    inference(avatar_contradiction_clause,[],[f1057])).
% 29.39/4.09  fof(f1057,plain,(
% 29.39/4.09    $false | spl14_46),
% 29.39/4.09    inference(subsumption_resolution,[],[f1056,f68])).
% 29.39/4.09  fof(f1056,plain,(
% 29.39/4.09    ~v1_relat_1(sK2) | spl14_46),
% 29.39/4.09    inference(subsumption_resolution,[],[f1051,f69])).
% 29.39/4.10  fof(f1051,plain,(
% 29.39/4.10    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl14_46),
% 29.39/4.10    inference(resolution,[],[f1042,f91])).
% 29.39/4.10  fof(f91,plain,(
% 29.39/4.10    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 29.39/4.10    inference(cnf_transformation,[],[f49])).
% 29.39/4.10  fof(f49,plain,(
% 29.39/4.10    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(flattening,[],[f48])).
% 29.39/4.10  fof(f48,plain,(
% 29.39/4.10    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(nnf_transformation,[],[f22])).
% 29.39/4.10  fof(f22,plain,(
% 29.39/4.10    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(ennf_transformation,[],[f6])).
% 29.39/4.10  fof(f6,axiom,(
% 29.39/4.10    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 29.39/4.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).
% 29.39/4.10  fof(f1042,plain,(
% 29.39/4.10    ~v6_relat_2(sK2) | spl14_46),
% 29.39/4.10    inference(avatar_component_clause,[],[f1040])).
% 29.39/4.10  fof(f1040,plain,(
% 29.39/4.10    spl14_46 <=> v6_relat_2(sK2)),
% 29.39/4.10    introduced(avatar_definition,[new_symbols(naming,[spl14_46])])).
% 29.39/4.10  fof(f1046,plain,(
% 29.39/4.10    ~spl14_46 | spl14_47),
% 29.39/4.10    inference(avatar_split_clause,[],[f1038,f1044,f1040])).
% 29.39/4.10  fof(f1038,plain,(
% 29.39/4.10    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~v6_relat_2(sK2) | r2_hidden(k4_tarski(X1,X0),sK2)) )),
% 29.39/4.10    inference(resolution,[],[f78,f68])).
% 29.39/4.10  fof(f78,plain,(
% 29.39/4.10    ( ! [X4,X0,X3] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | r2_hidden(k4_tarski(X4,X3),X0)) )),
% 29.39/4.10    inference(cnf_transformation,[],[f43])).
% 29.39/4.10  fof(f43,plain,(
% 29.39/4.10    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0) & ~r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) & sK5(X0) != sK6(X0) & r2_hidden(sK6(X0),k3_relat_1(X0)) & r2_hidden(sK5(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f41,f42])).
% 29.39/4.10  fof(f42,plain,(
% 29.39/4.10    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0) & ~r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) & sK5(X0) != sK6(X0) & r2_hidden(sK6(X0),k3_relat_1(X0)) & r2_hidden(sK5(X0),k3_relat_1(X0))))),
% 29.39/4.10    introduced(choice_axiom,[])).
% 29.39/4.10  fof(f41,plain,(
% 29.39/4.10    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(rectify,[],[f40])).
% 29.39/4.10  fof(f40,plain,(
% 29.39/4.10    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(nnf_transformation,[],[f19])).
% 29.39/4.10  fof(f19,plain,(
% 29.39/4.10    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(ennf_transformation,[],[f9])).
% 29.39/4.10  fof(f9,axiom,(
% 29.39/4.10    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 29.39/4.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).
% 29.39/4.10  fof(f524,plain,(
% 29.39/4.10    spl14_32),
% 29.39/4.10    inference(avatar_contradiction_clause,[],[f523])).
% 29.39/4.10  fof(f523,plain,(
% 29.39/4.10    $false | spl14_32),
% 29.39/4.10    inference(subsumption_resolution,[],[f522,f68])).
% 29.39/4.10  fof(f522,plain,(
% 29.39/4.10    ~v1_relat_1(sK2) | spl14_32),
% 29.39/4.10    inference(subsumption_resolution,[],[f518,f69])).
% 29.39/4.10  fof(f518,plain,(
% 29.39/4.10    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl14_32),
% 29.39/4.10    inference(resolution,[],[f510,f89])).
% 29.39/4.10  fof(f89,plain,(
% 29.39/4.10    ( ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 29.39/4.10    inference(cnf_transformation,[],[f49])).
% 29.39/4.10  fof(f510,plain,(
% 29.39/4.10    ~v8_relat_2(sK2) | spl14_32),
% 29.39/4.10    inference(avatar_component_clause,[],[f508])).
% 29.39/4.10  fof(f508,plain,(
% 29.39/4.10    spl14_32 <=> v8_relat_2(sK2)),
% 29.39/4.10    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).
% 29.39/4.10  fof(f514,plain,(
% 29.39/4.10    ~spl14_32 | spl14_33),
% 29.39/4.10    inference(avatar_split_clause,[],[f506,f512,f508])).
% 29.39/4.10  fof(f506,plain,(
% 29.39/4.10    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(k4_tarski(X2,X0),sK2) | ~v8_relat_2(sK2) | r2_hidden(k4_tarski(X2,X1),sK2)) )),
% 29.39/4.10    inference(resolution,[],[f84,f68])).
% 29.39/4.10  fof(f84,plain,(
% 29.39/4.10    ( ! [X6,X4,X0,X5] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~v8_relat_2(X0) | r2_hidden(k4_tarski(X4,X6),X0)) )),
% 29.39/4.10    inference(cnf_transformation,[],[f47])).
% 29.39/4.10  fof(f47,plain,(
% 29.39/4.10    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0) & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f45,f46])).
% 29.39/4.10  fof(f46,plain,(
% 29.39/4.10    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0) & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0)))),
% 29.39/4.10    introduced(choice_axiom,[])).
% 29.39/4.10  fof(f45,plain,(
% 29.39/4.10    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(rectify,[],[f44])).
% 29.39/4.10  fof(f44,plain,(
% 29.39/4.10    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(nnf_transformation,[],[f21])).
% 29.39/4.10  fof(f21,plain,(
% 29.39/4.10    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(flattening,[],[f20])).
% 29.39/4.10  fof(f20,plain,(
% 29.39/4.10    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(ennf_transformation,[],[f7])).
% 29.39/4.10  fof(f7,axiom,(
% 29.39/4.10    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 29.39/4.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).
% 29.39/4.10  fof(f413,plain,(
% 29.39/4.10    spl14_22),
% 29.39/4.10    inference(avatar_contradiction_clause,[],[f412])).
% 29.39/4.10  fof(f412,plain,(
% 29.39/4.10    $false | spl14_22),
% 29.39/4.10    inference(subsumption_resolution,[],[f411,f68])).
% 29.39/4.10  fof(f411,plain,(
% 29.39/4.10    ~v1_relat_1(sK2) | spl14_22),
% 29.39/4.10    inference(subsumption_resolution,[],[f408,f69])).
% 29.39/4.10  fof(f408,plain,(
% 29.39/4.10    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl14_22),
% 29.39/4.10    inference(resolution,[],[f401,f90])).
% 29.39/4.10  fof(f90,plain,(
% 29.39/4.10    ( ! [X0] : (v4_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 29.39/4.10    inference(cnf_transformation,[],[f49])).
% 29.39/4.10  fof(f401,plain,(
% 29.39/4.10    ~v4_relat_2(sK2) | spl14_22),
% 29.39/4.10    inference(avatar_component_clause,[],[f399])).
% 29.39/4.10  fof(f399,plain,(
% 29.39/4.10    spl14_22 <=> v4_relat_2(sK2)),
% 29.39/4.10    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).
% 29.39/4.10  fof(f405,plain,(
% 29.39/4.10    ~spl14_22 | spl14_23),
% 29.39/4.10    inference(avatar_split_clause,[],[f397,f403,f399])).
% 29.39/4.10  fof(f397,plain,(
% 29.39/4.10    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(k4_tarski(X1,X0),sK2) | ~v4_relat_2(sK2) | X0 = X1) )),
% 29.39/4.10    inference(resolution,[],[f74,f68])).
% 29.39/4.10  fof(f74,plain,(
% 29.39/4.10    ( ! [X4,X0,X3] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~v4_relat_2(X0) | X3 = X4) )),
% 29.39/4.10    inference(cnf_transformation,[],[f39])).
% 29.39/4.10  fof(f39,plain,(
% 29.39/4.10    ! [X0] : (((v4_relat_2(X0) | (sK3(X0) != sK4(X0) & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f38])).
% 29.39/4.10  fof(f38,plain,(
% 29.39/4.10    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK3(X0) != sK4(X0) & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)))),
% 29.39/4.10    introduced(choice_axiom,[])).
% 29.39/4.10  fof(f37,plain,(
% 29.39/4.10    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(rectify,[],[f36])).
% 29.39/4.10  fof(f36,plain,(
% 29.39/4.10    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(nnf_transformation,[],[f18])).
% 29.39/4.10  fof(f18,plain,(
% 29.39/4.10    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(flattening,[],[f17])).
% 29.39/4.10  fof(f17,plain,(
% 29.39/4.10    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 29.39/4.10    inference(ennf_transformation,[],[f8])).
% 29.39/4.10  fof(f8,axiom,(
% 29.39/4.10    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 29.39/4.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).
% 29.39/4.10  fof(f315,plain,(
% 29.39/4.10    ~spl14_17),
% 29.39/4.10    inference(avatar_contradiction_clause,[],[f314])).
% 29.39/4.10  fof(f314,plain,(
% 29.39/4.10    $false | ~spl14_17),
% 29.39/4.10    inference(subsumption_resolution,[],[f313,f192])).
% 29.39/4.10  fof(f313,plain,(
% 29.39/4.10    ~r1_tarski(k1_wellord1(sK2,k3_relat_1(sK2)),sK11(sK2,k1_wellord1(sK2,k3_relat_1(sK2)))) | ~spl14_17),
% 29.39/4.10    inference(resolution,[],[f297,f113])).
% 29.39/4.10  fof(f297,plain,(
% 29.39/4.10    r2_hidden(sK11(sK2,k1_wellord1(sK2,k3_relat_1(sK2))),k1_wellord1(sK2,k3_relat_1(sK2))) | ~spl14_17),
% 29.39/4.10    inference(avatar_component_clause,[],[f295])).
% 29.39/4.10  fof(f295,plain,(
% 29.39/4.10    spl14_17 <=> r2_hidden(sK11(sK2,k1_wellord1(sK2,k3_relat_1(sK2))),k1_wellord1(sK2,k3_relat_1(sK2)))),
% 29.39/4.10    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).
% 29.39/4.10  fof(f302,plain,(
% 29.39/4.10    spl14_17 | spl14_18),
% 29.39/4.10    inference(avatar_split_clause,[],[f292,f299,f295])).
% 29.39/4.10  fof(f292,plain,(
% 29.39/4.10    k1_xboole_0 = k1_wellord1(sK2,k3_relat_1(sK2)) | r2_hidden(sK11(sK2,k1_wellord1(sK2,k3_relat_1(sK2))),k1_wellord1(sK2,k3_relat_1(sK2)))),
% 29.39/4.10    inference(resolution,[],[f192,f266])).
% 29.39/4.10  fof(f131,plain,(
% 29.39/4.10    spl14_1 | spl14_2),
% 29.39/4.10    inference(avatar_split_clause,[],[f72,f127,f123])).
% 29.39/4.10  fof(f72,plain,(
% 29.39/4.10    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 29.39/4.10    inference(cnf_transformation,[],[f35])).
% 29.39/4.10  fof(f130,plain,(
% 29.39/4.10    ~spl14_1 | ~spl14_2),
% 29.39/4.10    inference(avatar_split_clause,[],[f73,f127,f123])).
% 29.39/4.10  fof(f73,plain,(
% 29.39/4.10    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 29.39/4.10    inference(cnf_transformation,[],[f35])).
% 29.39/4.10  % SZS output end Proof for theBenchmark
% 29.39/4.10  % (32733)------------------------------
% 29.39/4.10  % (32733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.39/4.10  % (32733)Termination reason: Refutation
% 29.39/4.10  
% 29.39/4.10  % (32733)Memory used [KB]: 27376
% 29.39/4.10  % (32733)Time elapsed: 3.677 s
% 29.39/4.10  % (32733)------------------------------
% 29.39/4.10  % (32733)------------------------------
% 29.39/4.10  % (32729)Success in time 3.752 s
%------------------------------------------------------------------------------
