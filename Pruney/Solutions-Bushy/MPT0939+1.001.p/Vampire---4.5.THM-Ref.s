%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0939+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 390 expanded)
%              Number of leaves         :   26 ( 130 expanded)
%              Depth                    :   16
%              Number of atoms          :  523 (2096 expanded)
%              Number of equality atoms :   37 ( 276 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f100,f108,f115,f121,f123,f150,f179,f192,f199,f213,f223,f231,f238])).

fof(f238,plain,
    ( ~ spl5_22
    | spl5_4
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f234,f171,f103,f211])).

fof(f211,plain,
    ( spl5_22
  <=> v1_relat_1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f103,plain,
    ( spl5_4
  <=> r6_relat_2(k1_wellord2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f171,plain,
    ( spl5_14
  <=> r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f234,plain,
    ( r6_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_14 ),
    inference(resolution,[],[f172,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r6_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
              & sK1(X0,X1) != sK2(X0,X1)
              & r2_hidden(sK2(X0,X1),X1)
              & r2_hidden(sK1(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & X2 != X3
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
        & sK1(X0,X1) != sK2(X0,X1)
        & r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | X2 = X3
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r6_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | X2 = X3
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r6_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_2)).

fof(f172,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f171])).

fof(f231,plain,
    ( ~ spl5_10
    | ~ spl5_16
    | spl5_15
    | spl5_18 ),
    inference(avatar_split_clause,[],[f227,f187,f174,f177,f134])).

fof(f134,plain,
    ( spl5_10
  <=> v3_ordinal1(sK1(k1_wellord2(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f177,plain,
    ( spl5_16
  <=> v3_ordinal1(sK2(k1_wellord2(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f174,plain,
    ( spl5_15
  <=> r1_ordinal1(sK1(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f187,plain,
    ( spl5_18
  <=> r1_ordinal1(sK2(k1_wellord2(sK0),sK0),sK1(k1_wellord2(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f227,plain,
    ( r1_ordinal1(sK1(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0))
    | ~ v3_ordinal1(sK2(k1_wellord2(sK0),sK0))
    | ~ v3_ordinal1(sK1(k1_wellord2(sK0),sK0))
    | spl5_18 ),
    inference(resolution,[],[f198,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f198,plain,
    ( ~ r1_ordinal1(sK2(k1_wellord2(sK0),sK0),sK1(k1_wellord2(sK0),sK0))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f187])).

fof(f223,plain,(
    spl5_22 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | spl5_22 ),
    inference(resolution,[],[f212,f37])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f212,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f211])).

fof(f213,plain,
    ( ~ spl5_22
    | spl5_4
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f201,f196,f103,f211])).

fof(f196,plain,
    ( spl5_19
  <=> r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK1(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f201,plain,
    ( r6_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_19 ),
    inference(resolution,[],[f197,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | r6_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f197,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK1(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f196])).

fof(f199,plain,
    ( spl5_1
    | spl5_19
    | ~ spl5_18
    | ~ spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f194,f119,f134,f187,f196,f66])).

fof(f66,plain,
    ( spl5_1
  <=> v6_relat_2(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f119,plain,
    ( spl5_7
  <=> ! [X0] :
        ( ~ r1_ordinal1(sK2(k1_wellord2(sK0),sK0),X0)
        | r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
        | ~ v3_ordinal1(X0)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f194,plain,
    ( ~ v3_ordinal1(sK1(k1_wellord2(sK0),sK0))
    | ~ r1_ordinal1(sK2(k1_wellord2(sK0),sK0),sK1(k1_wellord2(sK0),sK0))
    | r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK1(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))
    | v6_relat_2(k1_wellord2(sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f124,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r6_relat_2(k1_wellord2(X0),X0)
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(global_subsumption,[],[f37,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r6_relat_2(k1_wellord2(X0),X0)
      | v6_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f39,f75])).

fof(f75,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f37,f64])).

fof(f64,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & r2_hidden(sK4(X0,X1),X0)
            & r2_hidden(sK3(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f39,plain,(
    ! [X0] :
      ( ~ r6_relat_2(X0,k3_relat_1(X0))
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ~ r6_relat_2(X0,k3_relat_1(X0)) )
        & ( r6_relat_2(X0,k3_relat_1(X0))
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_2)).

fof(f124,plain,
    ( ! [X0] :
        ( r6_relat_2(k1_wellord2(X0),sK0)
        | ~ v3_ordinal1(sK1(k1_wellord2(X0),sK0))
        | ~ r1_ordinal1(sK2(k1_wellord2(sK0),sK0),sK1(k1_wellord2(X0),sK0))
        | r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK1(k1_wellord2(X0),sK0)),k1_wellord2(sK0)) )
    | ~ spl5_7 ),
    inference(resolution,[],[f120,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k1_wellord2(X0),X1),X1)
      | r6_relat_2(k1_wellord2(X0),X1) ) ),
    inference(resolution,[],[f41,f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK1(X0,X1),X1)
      | r6_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
        | ~ v3_ordinal1(X0)
        | ~ r1_ordinal1(sK2(k1_wellord2(sK0),sK0),X0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f192,plain,
    ( spl5_4
    | ~ spl5_2
    | spl5_16 ),
    inference(avatar_split_clause,[],[f191,f177,f70,f103])).

fof(f70,plain,
    ( spl5_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f191,plain,
    ( ~ v3_ordinal1(sK0)
    | r6_relat_2(k1_wellord2(sK0),sK0)
    | spl5_16 ),
    inference(resolution,[],[f190,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(k1_wellord2(X0),X1),X1)
      | r6_relat_2(k1_wellord2(X0),X1) ) ),
    inference(resolution,[],[f79,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X1)
      | r6_relat_2(k1_wellord2(X0),X1) ) ),
    inference(resolution,[],[f42,f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | r6_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(k1_wellord2(sK0),sK0),X0)
        | ~ v3_ordinal1(X0) )
    | spl5_16 ),
    inference(resolution,[],[f178,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_ordinal1(X1)
          | ~ m1_subset_1(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_ordinal1)).

fof(f178,plain,
    ( ~ v3_ordinal1(sK2(k1_wellord2(sK0),sK0))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,
    ( spl5_1
    | spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f169,f106,f177,f174,f171,f66])).

fof(f106,plain,
    ( spl5_5
  <=> ! [X0] :
        ( ~ r1_ordinal1(sK1(k1_wellord2(sK0),sK0),X0)
        | r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
        | ~ v3_ordinal1(X0)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f169,plain,
    ( ~ v3_ordinal1(sK2(k1_wellord2(sK0),sK0))
    | ~ r1_ordinal1(sK1(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0))
    | r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))
    | v6_relat_2(k1_wellord2(sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f110,f77])).

fof(f110,plain,
    ( ! [X1] :
        ( r6_relat_2(k1_wellord2(X1),sK0)
        | ~ v3_ordinal1(sK2(k1_wellord2(X1),sK0))
        | ~ r1_ordinal1(sK1(k1_wellord2(sK0),sK0),sK2(k1_wellord2(X1),sK0))
        | r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),sK2(k1_wellord2(X1),sK0)),k1_wellord2(sK0)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f107,f79])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
        | ~ v3_ordinal1(X0)
        | ~ r1_ordinal1(sK1(k1_wellord2(sK0),sK0),X0) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f150,plain,
    ( spl5_4
    | ~ spl5_2
    | spl5_10 ),
    inference(avatar_split_clause,[],[f148,f134,f70,f103])).

fof(f148,plain,
    ( ~ v3_ordinal1(sK0)
    | r6_relat_2(k1_wellord2(sK0),sK0)
    | spl5_10 ),
    inference(resolution,[],[f147,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(k1_wellord2(X0),X1),X1)
      | r6_relat_2(k1_wellord2(X0),X1) ) ),
    inference(resolution,[],[f78,f54])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1(k1_wellord2(sK0),sK0),X0)
        | ~ v3_ordinal1(X0) )
    | spl5_10 ),
    inference(resolution,[],[f135,f46])).

fof(f135,plain,
    ( ~ v3_ordinal1(sK1(k1_wellord2(sK0),sK0))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f123,plain,
    ( spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f122,f103,f66])).

fof(f122,plain,
    ( v6_relat_2(k1_wellord2(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f104,f77])).

fof(f104,plain,
    ( r6_relat_2(k1_wellord2(sK0),sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f121,plain,
    ( spl5_4
    | spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f117,f113,f119,f103])).

fof(f113,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( ~ v3_ordinal1(X0)
        | ~ r1_ordinal1(sK2(k1_wellord2(sK0),sK0),X0)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),X1)
        | r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),X0),k1_wellord2(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ r1_ordinal1(sK2(k1_wellord2(sK0),sK0),X0)
        | ~ r2_hidden(X0,sK0)
        | ~ v3_ordinal1(X0)
        | r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
        | r6_relat_2(k1_wellord2(sK0),sK0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f114,f79])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),X1)
        | ~ r1_ordinal1(sK2(k1_wellord2(sK0),sK0),X0)
        | ~ r2_hidden(X0,X1)
        | ~ v3_ordinal1(X0)
        | r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),X0),k1_wellord2(X1)) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl5_1
    | spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f111,f70,f113,f66])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),X0),k1_wellord2(X1))
        | ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),X1)
        | ~ r2_hidden(X0,X1)
        | ~ r1_ordinal1(sK2(k1_wellord2(sK0),sK0),X0)
        | v6_relat_2(k1_wellord2(sK0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f94,f77])).

fof(f94,plain,
    ( ! [X4,X5,X3] :
        ( r6_relat_2(k1_wellord2(X3),sK0)
        | ~ v3_ordinal1(X4)
        | r2_hidden(k4_tarski(sK2(k1_wellord2(X3),sK0),X4),k1_wellord2(X5))
        | ~ r2_hidden(sK2(k1_wellord2(X3),sK0),X5)
        | ~ r2_hidden(X4,X5)
        | ~ r1_ordinal1(sK2(k1_wellord2(X3),sK0),X4) )
    | ~ spl5_2 ),
    inference(resolution,[],[f91,f83])).

fof(f91,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ r1_ordinal1(X0,X2)
        | ~ v3_ordinal1(X2)
        | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f90,f71])).

fof(f71,plain,
    ( v3_ordinal1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f90,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ v3_ordinal1(X5)
      | ~ r2_hidden(X4,X3)
      | ~ r1_ordinal1(X4,X2)
      | ~ v3_ordinal1(X2)
      | r2_hidden(k4_tarski(X4,X2),k1_wellord2(X3))
      | ~ m1_subset_1(X4,X5)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f88,f46])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) ) ),
    inference(resolution,[],[f73,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f73,plain,(
    ! [X4,X0,X5] :
      ( ~ r1_tarski(X4,X5)
      | r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(global_subsumption,[],[f37,f62])).

fof(f62,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f108,plain,
    ( spl5_4
    | spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f101,f98,f106,f103])).

fof(f98,plain,
    ( spl5_3
  <=> ! [X1,X0] :
        ( ~ v3_ordinal1(X0)
        | ~ r1_ordinal1(sK1(k1_wellord2(sK0),sK0),X0)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(sK1(k1_wellord2(sK0),sK0),X1)
        | r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r1_ordinal1(sK1(k1_wellord2(sK0),sK0),X0)
        | ~ r2_hidden(X0,sK0)
        | ~ v3_ordinal1(X0)
        | r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
        | r6_relat_2(k1_wellord2(sK0),sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f99,f78])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1(k1_wellord2(sK0),sK0),X1)
        | ~ r1_ordinal1(sK1(k1_wellord2(sK0),sK0),X0)
        | ~ r2_hidden(X0,X1)
        | ~ v3_ordinal1(X0)
        | r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(X1)) )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,
    ( spl5_1
    | spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f95,f70,f98,f66])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(X1))
        | ~ r2_hidden(sK1(k1_wellord2(sK0),sK0),X1)
        | ~ r2_hidden(X0,X1)
        | ~ r1_ordinal1(sK1(k1_wellord2(sK0),sK0),X0)
        | v6_relat_2(k1_wellord2(sK0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f93,f77])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( r6_relat_2(k1_wellord2(X0),sK0)
        | ~ v3_ordinal1(X1)
        | r2_hidden(k4_tarski(sK1(k1_wellord2(X0),sK0),X1),k1_wellord2(X2))
        | ~ r2_hidden(sK1(k1_wellord2(X0),sK0),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r1_ordinal1(sK1(k1_wellord2(X0),sK0),X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f91,f82])).

fof(f72,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ v6_relat_2(k1_wellord2(sK0))
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ~ v6_relat_2(k1_wellord2(X0))
        & v3_ordinal1(X0) )
   => ( ~ v6_relat_2(k1_wellord2(sK0))
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v6_relat_2(k1_wellord2(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v6_relat_2(k1_wellord2(X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v6_relat_2(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_wellord2)).

fof(f68,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    ~ v6_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
