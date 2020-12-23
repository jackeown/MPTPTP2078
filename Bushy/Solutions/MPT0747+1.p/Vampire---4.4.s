%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t37_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:26 EDT 2019

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 223 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  371 ( 881 expanded)
%              Number of equality atoms :   24 (  65 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16798,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1387,f1534,f2251,f2258,f2308,f4707,f16638,f16697,f16796])).

fof(f16796,plain,
    ( spl6_351
    | ~ spl6_1062 ),
    inference(avatar_contradiction_clause,[],[f16795])).

fof(f16795,plain,
    ( $false
    | ~ spl6_351
    | ~ spl6_1062 ),
    inference(subsumption_resolution,[],[f16786,f4665])).

fof(f4665,plain,
    ( ~ v2_ordinal1(sK0)
    | ~ spl6_351 ),
    inference(avatar_component_clause,[],[f4664])).

fof(f4664,plain,
    ( spl6_351
  <=> ~ v2_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_351])])).

fof(f16786,plain,
    ( v2_ordinal1(sK0)
    | ~ spl6_1062 ),
    inference(trivial_inequality_removal,[],[f16780])).

fof(f16780,plain,
    ( sK2(sK0) != sK2(sK0)
    | v2_ordinal1(sK0)
    | ~ spl6_1062 ),
    inference(superposition,[],[f74,f16637])).

fof(f16637,plain,
    ( sK2(sK0) = sK3(sK0)
    | ~ spl6_1062 ),
    inference(avatar_component_clause,[],[f16636])).

fof(f16636,plain,
    ( spl6_1062
  <=> sK2(sK0) = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1062])])).

fof(f74,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK3(X0),sK2(X0))
          & sK2(X0) != sK3(X0)
          & ~ r2_hidden(sK2(X0),sK3(X0))
          & r2_hidden(sK3(X0),X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK3(X0),sK2(X0))
        & sK2(X0) != sK3(X0)
        & ~ r2_hidden(sK2(X0),sK3(X0))
        & r2_hidden(sK3(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(X2,X1)
            | X1 = X2
            | r2_hidden(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',d3_ordinal1)).

fof(f16697,plain,
    ( spl6_351
    | ~ spl6_1060 ),
    inference(avatar_contradiction_clause,[],[f16696])).

fof(f16696,plain,
    ( $false
    | ~ spl6_351
    | ~ spl6_1060 ),
    inference(subsumption_resolution,[],[f16683,f4665])).

fof(f16683,plain,
    ( v2_ordinal1(sK0)
    | ~ spl6_1060 ),
    inference(resolution,[],[f16631,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK2(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f16631,plain,
    ( r2_hidden(sK3(sK0),sK2(sK0))
    | ~ spl6_1060 ),
    inference(avatar_component_clause,[],[f16630])).

fof(f16630,plain,
    ( spl6_1060
  <=> r2_hidden(sK3(sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1060])])).

fof(f16638,plain,
    ( spl6_1060
    | spl6_1062
    | ~ spl6_180
    | ~ spl6_182
    | spl6_351 ),
    inference(avatar_split_clause,[],[f16625,f4664,f2256,f2249,f16636,f16630])).

fof(f2249,plain,
    ( spl6_180
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_180])])).

fof(f2256,plain,
    ( spl6_182
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_182])])).

fof(f16625,plain,
    ( sK2(sK0) = sK3(sK0)
    | r2_hidden(sK3(sK0),sK2(sK0))
    | ~ spl6_180
    | ~ spl6_182
    | ~ spl6_351 ),
    inference(subsumption_resolution,[],[f16624,f4665])).

fof(f16624,plain,
    ( sK2(sK0) = sK3(sK0)
    | r2_hidden(sK3(sK0),sK2(sK0))
    | v2_ordinal1(sK0)
    | ~ spl6_180
    | ~ spl6_182 ),
    inference(subsumption_resolution,[],[f16551,f2257])).

fof(f2257,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl6_182 ),
    inference(avatar_component_clause,[],[f2256])).

fof(f16551,plain,
    ( sK2(sK0) = sK3(sK0)
    | ~ r2_hidden(sK3(sK0),sK0)
    | r2_hidden(sK3(sK0),sK2(sK0))
    | v2_ordinal1(sK0)
    | ~ spl6_180 ),
    inference(resolution,[],[f2329,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2329,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0),X0)
        | sK2(sK0) = X0
        | ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK2(sK0)) )
    | ~ spl6_180 ),
    inference(resolution,[],[f2250,f936])).

fof(f936,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,sK0)
      | X3 = X4
      | r2_hidden(X4,X3)
      | ~ r2_hidden(X3,sK0)
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f614,f61])).

fof(f61,plain,(
    ! [X1] :
      ( v3_ordinal1(X1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X1] :
      ( ( r2_hidden(X1,sK0)
        | ~ v3_ordinal1(X1) )
      & ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f44,plain,
    ( ? [X0] :
      ! [X1] :
        ( ( r2_hidden(X1,X0)
          | ~ v3_ordinal1(X1) )
        & ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,X0) ) )
   => ! [X1] :
        ( ( r2_hidden(X1,sK0)
          | ~ v3_ordinal1(X1) )
        & ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
    ! [X1] :
      ( ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
      & ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
    <=> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( r2_hidden(X1,X0)
          <=> v3_ordinal1(X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',t37_ordinal1)).

fof(f614,plain,(
    ! [X4,X3] :
      ( ~ v3_ordinal1(X4)
      | r2_hidden(X3,X4)
      | X3 = X4
      | r2_hidden(X4,X3)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(resolution,[],[f64,f61])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',t24_ordinal1)).

fof(f2250,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl6_180 ),
    inference(avatar_component_clause,[],[f2249])).

fof(f4707,plain,
    ( ~ spl6_0
    | spl6_19
    | ~ spl6_350 ),
    inference(avatar_contradiction_clause,[],[f4706])).

fof(f4706,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_19
    | ~ spl6_350 ),
    inference(subsumption_resolution,[],[f4705,f114])).

fof(f114,plain,
    ( v1_ordinal1(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_0
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f4705,plain,
    ( ~ v1_ordinal1(sK0)
    | ~ spl6_19
    | ~ spl6_350 ),
    inference(subsumption_resolution,[],[f4704,f568])).

fof(f568,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f567])).

fof(f567,plain,
    ( spl6_19
  <=> ~ v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f4704,plain,
    ( v3_ordinal1(sK0)
    | ~ v1_ordinal1(sK0)
    | ~ spl6_350 ),
    inference(resolution,[],[f4668,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | v3_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',cc2_ordinal1)).

fof(f4668,plain,
    ( v2_ordinal1(sK0)
    | ~ spl6_350 ),
    inference(avatar_component_clause,[],[f4667])).

fof(f4667,plain,
    ( spl6_350
  <=> v2_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_350])])).

fof(f2308,plain,(
    ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f2307])).

fof(f2307,plain,
    ( $false
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f2306,f565])).

fof(f565,plain,
    ( v3_ordinal1(sK0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f564])).

fof(f564,plain,
    ( spl6_18
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f2306,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ spl6_18 ),
    inference(resolution,[],[f2298,f62])).

fof(f62,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2298,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ spl6_18 ),
    inference(resolution,[],[f565,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | ~ r2_hidden(sK0,X0) ) ),
    inference(resolution,[],[f79,f62])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',antisymmetry_r2_hidden)).

fof(f2258,plain,
    ( spl6_182
    | spl6_18
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f1535,f113,f564,f2256])).

fof(f1535,plain,
    ( v3_ordinal1(sK0)
    | r2_hidden(sK3(sK0),sK0)
    | ~ spl6_0 ),
    inference(resolution,[],[f114,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_ordinal1(X0)
      | v3_ordinal1(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(resolution,[],[f72,f66])).

fof(f72,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2251,plain,
    ( spl6_180
    | spl6_18
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f1536,f113,f564,f2249])).

fof(f1536,plain,
    ( v3_ordinal1(sK0)
    | r2_hidden(sK2(sK0),sK0)
    | ~ spl6_0 ),
    inference(resolution,[],[f114,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_ordinal1(X0)
      | v3_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(resolution,[],[f71,f66])).

fof(f71,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1534,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f1533])).

fof(f1533,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f1531,f1514])).

fof(f1514,plain,
    ( r2_hidden(sK1(sK0),sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f111,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK1(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK1(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',d2_ordinal1)).

fof(f111,plain,
    ( ~ v1_ordinal1(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_1
  <=> ~ v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1531,plain,
    ( ~ r2_hidden(sK1(sK0),sK0)
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f1526,f61])).

fof(f1526,plain,
    ( ~ v3_ordinal1(sK1(sK0))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f1512,f122])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1(sK0),sK0),X0)
        | ~ v3_ordinal1(X0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f120,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',t23_ordinal1)).

fof(f120,plain,
    ( ~ v3_ordinal1(sK5(sK1(sK0),sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_3
  <=> ~ v3_ordinal1(sK5(sK1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1512,plain,
    ( r2_hidden(sK5(sK1(sK0),sK0),sK1(sK0))
    | ~ spl6_1 ),
    inference(resolution,[],[f111,f106])).

fof(f106,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK5(sK1(X0),X0),sK1(X0)) ) ),
    inference(resolution,[],[f82,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',d3_tarski)).

fof(f1387,plain,
    ( spl6_0
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f1386,f119,f113])).

fof(f1386,plain,
    ( ~ v3_ordinal1(sK5(sK1(sK0),sK0))
    | v1_ordinal1(sK0) ),
    inference(resolution,[],[f107,f69])).

fof(f107,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK0)
      | ~ v3_ordinal1(sK5(X0,sK0)) ) ),
    inference(resolution,[],[f83,f62])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
