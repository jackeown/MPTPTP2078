%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 201 expanded)
%              Number of leaves         :   10 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  337 (1439 expanded)
%              Number of equality atoms :   55 ( 258 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f62,f87,f100,f113])).

fof(f113,plain,
    ( ~ spl5_1
    | spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f108,f103])).

fof(f103,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl5_2
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f26,f60,f55,f44])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
                | sK3(X0,X1,X2) = X1
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
                  & sK3(X0,X1,X2) != X1 )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
          | sK3(X0,X1,X2) = X1
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
            & sK3(X0,X1,X2) != X1 )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f55,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_2
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f60,plain,
    ( sK0 != sK1
    | spl5_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
        & sK0 != sK1 )
      | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
    & ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
      | sK0 = sK1
      | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
            & X0 != X1 )
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1
          | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
          & sK0 != sK1 )
        | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
      & ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
        | sK0 = sK1
        | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
          & X0 != X1 )
        | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & ( r2_hidden(X0,k1_wellord1(X2,X1))
        | X0 = X1
        | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
          & X0 != X1 )
        | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & ( r2_hidden(X0,k1_wellord1(X2,X1))
        | X0 = X1
        | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <~> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <~> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
              | X0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
            | X0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_wellord1)).

fof(f108,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f50,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_wellord1(X2)
      | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

fof(f50,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_1
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f29,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f95,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f95,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl5_1
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f51,f59])).

fof(f59,plain,
    ( sK0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f51,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f87,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f85,f26])).

fof(f85,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f84,f27])).

fof(f84,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f83,f28])).

fof(f83,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f82,f29])).

fof(f82,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f79,f70])).

fof(f70,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f26,f54,f45])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f79,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1 ),
    inference(resolution,[],[f42,f51])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,
    ( spl5_1
    | spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f30,f53,f58,f49])).

fof(f30,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | sK0 = sK1
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f31,f58,f49])).

fof(f31,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f32,f53,f49])).

fof(f32,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (25843)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.48  % (25850)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.49  % (25836)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (25848)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.49  % (25836)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f56,f61,f62,f87,f100,f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ~spl5_1 | spl5_2 | spl5_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    $false | (~spl5_1 | spl5_2 | spl5_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f108,f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | (spl5_2 | spl5_3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f26,f60,f55,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | r2_hidden(X4,k1_wellord1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) | sK3(X0,X1,X2) = X1 | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) & sK3(X0,X1,X2) != X1) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) | sK3(X0,X1,X2) = X1 | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) & sK3(X0,X1,X2) != X1) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(rectify,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_wellord1(sK2,sK1)) | spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl5_2 <=> r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    sK0 != sK1 | spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl5_3 <=> sK0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ((~r2_hidden(sK0,k1_wellord1(sK2,sK1)) & sK0 != sK1) | ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))) & (r2_hidden(sK0,k1_wellord1(sK2,sK1)) | sK0 = sK1 | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (((~r2_hidden(X0,k1_wellord1(X2,X1)) & X0 != X1) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1 | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => (((~r2_hidden(sK0,k1_wellord1(sK2,sK1)) & sK0 != sK1) | ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))) & (r2_hidden(sK0,k1_wellord1(sK2,sK1)) | sK0 = sK1 | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (((~r2_hidden(X0,k1_wellord1(X2,X1)) & X0 != X1) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1 | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((((~r2_hidden(X0,k1_wellord1(X2,X1)) & X0 != X1) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & ((r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1) | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <~> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <~> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1)) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_wellord1)).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl5_1),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f50,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_wellord1(X2) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | (~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl5_1 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    r2_hidden(sK1,k3_relat_1(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    r2_hidden(sK0,k3_relat_1(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v2_wellord1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl5_1 | ~spl5_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    $false | (spl5_1 | ~spl5_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f95,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.49    inference(resolution,[],[f41,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | (spl5_1 | ~spl5_3)),
% 0.21/0.49    inference(backward_demodulation,[],[f51,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    sK0 = sK1 | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl5_1 | ~spl5_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    $false | (spl5_1 | ~spl5_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f85,f26])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f84,f27])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f83,f28])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k3_relat_1(sK2)) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f82,f29])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f79,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl5_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f26,f54,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X4,X1),X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f53])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl5_1),
% 0.21/0.49    inference(resolution,[],[f42,f51])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl5_1 | spl5_3 | spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f53,f58,f49])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | sK0 = sK1 | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~spl5_1 | ~spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f58,f49])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    sK0 != sK1 | ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ~spl5_1 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f53,f49])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (25836)------------------------------
% 0.21/0.49  % (25836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (25836)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (25836)Memory used [KB]: 10746
% 0.21/0.49  % (25836)Time elapsed: 0.098 s
% 0.21/0.49  % (25836)------------------------------
% 0.21/0.49  % (25836)------------------------------
% 0.21/0.50  % (25824)Success in time 0.139 s
%------------------------------------------------------------------------------
