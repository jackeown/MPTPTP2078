%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 272 expanded)
%              Number of leaves         :   14 (  87 expanded)
%              Depth                    :   23
%              Number of atoms          :  453 (1772 expanded)
%              Number of equality atoms :   47 ( 169 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f207,f246,f252,f258,f263])).

fof(f263,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f261,f34])).

fof(f34,plain,(
    ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v2_funct_1(sK3)
    & r1_tarski(k2_relat_1(sK3),k1_relat_1(sK2))
    & v2_funct_1(k5_relat_1(sK3,sK2))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f8,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_funct_1(X1)
            & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
            & v2_funct_1(k5_relat_1(X1,X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(sK2))
          & v2_funct_1(k5_relat_1(X1,sK2))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ v2_funct_1(X1)
        & r1_tarski(k2_relat_1(X1),k1_relat_1(sK2))
        & v2_funct_1(k5_relat_1(X1,sK2))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_funct_1(sK3)
      & r1_tarski(k2_relat_1(sK3),k1_relat_1(sK2))
      & v2_funct_1(k5_relat_1(sK3,sK2))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v2_funct_1(k5_relat_1(X1,X0)) )
             => v2_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

fof(f261,plain,
    ( v2_funct_1(sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f260,f31])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f260,plain,
    ( ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f259,f30])).

fof(f30,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f259,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f206,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f43,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f12,f18,f17])).

fof(f17,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f206,plain,
    ( sP0(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl6_2
  <=> sP0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f258,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f256,f30])).

fof(f256,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f255,f31])).

fof(f255,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f254,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f254,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f253,f29])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f253,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_4 ),
    inference(resolution,[],[f245,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

% (27557)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f245,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK2))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl6_4
  <=> v1_relat_1(k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f252,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f250,f30])).

fof(f250,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f249,f31])).

fof(f249,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f248,f28])).

fof(f248,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f247,f29])).

fof(f247,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_3 ),
    inference(resolution,[],[f241,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f241,plain,
    ( ~ v1_funct_1(k5_relat_1(sK3,sK2))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl6_3
  <=> v1_funct_1(k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f246,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f237,f200,f243,f239])).

fof(f200,plain,
    ( spl6_1
  <=> sP0(k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f237,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK2))
    | ~ v1_funct_1(k5_relat_1(sK3,sK2))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f236,f32])).

fof(f32,plain,(
    v2_funct_1(k5_relat_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f236,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK2))
    | ~ v2_funct_1(k5_relat_1(sK3,sK2))
    | ~ v1_funct_1(k5_relat_1(sK3,sK2))
    | spl6_1 ),
    inference(resolution,[],[f202,f48])).

fof(f48,plain,(
    ! [X1] :
      ( sP0(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f43,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_funct_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f202,plain,
    ( ~ sP0(k5_relat_1(sK3,sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f200])).

fof(f207,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f198,f204,f200])).

fof(f198,plain,
    ( sP0(sK3)
    | ~ sP0(k5_relat_1(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f197,f30])).

fof(f197,plain,
    ( ~ v1_relat_1(sK3)
    | sP0(sK3)
    | ~ sP0(k5_relat_1(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f196,f31])).

fof(f196,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sP0(sK3)
    | ~ sP0(k5_relat_1(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f195,f28])).

fof(f195,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sP0(sK3)
    | ~ sP0(k5_relat_1(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f193,f29])).

fof(f193,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sP0(sK3)
    | ~ sP0(k5_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f192,f33])).

fof(f33,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP0(X0)
      | ~ sP0(k5_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f191,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK4(X0) != sK5(X0)
          & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
          & r2_hidden(sK5(X0),k1_relat_1(X0))
          & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ sP0(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP0(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f190,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ sP0(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP0(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ sP0(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP0(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f188,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1)))
      | ~ r2_hidden(sK4(X0),k1_relat_1(k5_relat_1(X0,X1)))
      | ~ sP0(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f187,f39])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1)))
      | ~ r2_hidden(sK4(X0),k1_relat_1(k5_relat_1(X0,X1)))
      | ~ sP0(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP0(X0)
      | ~ r2_hidden(sK4(X0),k1_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f167,f42])).

fof(f42,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f167,plain,(
    ! [X0,X1] :
      ( sK4(X0) = sK5(X0)
      | ~ r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1)))
      | ~ r2_hidden(sK4(X0),k1_relat_1(k5_relat_1(X0,X1)))
      | ~ sP0(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP0(X0)
      | ~ r2_hidden(sK4(X0),k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X2)) != k1_funct_1(X1,k1_funct_1(X0,sK4(X0)))
      | sK5(X0) = X2
      | ~ r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1)))
      | ~ sP0(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP0(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X2)) != k1_funct_1(X1,k1_funct_1(X0,sK4(X0)))
      | sK5(X0) = X2
      | ~ r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1)))
      | ~ sP0(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP0(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f80,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X0,X1),X2) != k1_funct_1(X1,k1_funct_1(X0,sK4(X0)))
      | sK5(X0) = X2
      | ~ r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1)))
      | ~ sP0(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f71,f40])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X0,X1),X2) != k1_funct_1(X1,k1_funct_1(X0,sK4(X0)))
      | sK5(X0) = X2
      | ~ r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1)))
      | ~ sP0(k5_relat_1(X0,X1))
      | ~ r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP0(X0) ) ),
    inference(superposition,[],[f61,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X4,X2,X5,X3] :
      ( k1_funct_1(X3,k1_funct_1(X2,X4)) != k1_funct_1(k5_relat_1(X2,X3),X5)
      | X4 = X5
      | ~ r2_hidden(X4,k1_relat_1(k5_relat_1(X2,X3)))
      | ~ r2_hidden(X5,k1_relat_1(k5_relat_1(X2,X3)))
      | ~ sP0(k5_relat_1(X2,X3))
      | ~ r2_hidden(X4,k1_relat_1(X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f38,f46])).

fof(f38,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:56:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (27546)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (27535)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (27532)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (27537)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (27533)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (27545)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (27534)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (27556)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (27536)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (27538)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (27542)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (27555)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (27547)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (27553)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (27548)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (27543)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (27549)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (27544)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (27539)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (27540)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (27550)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (27554)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (27541)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (27552)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.54  % (27551)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.55  % (27536)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f264,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f207,f246,f252,f258,f263])).
% 0.22/0.55  fof(f263,plain,(
% 0.22/0.55    ~spl6_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f262])).
% 0.22/0.55  fof(f262,plain,(
% 0.22/0.55    $false | ~spl6_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f261,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ~v2_funct_1(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    (~v2_funct_1(sK3) & r1_tarski(k2_relat_1(sK3),k1_relat_1(sK2)) & v2_funct_1(k5_relat_1(sK3,sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f8,f21,f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (~v2_funct_1(X1) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (~v2_funct_1(X1) & r1_tarski(k2_relat_1(X1),k1_relat_1(sK2)) & v2_funct_1(k5_relat_1(X1,sK2)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ? [X1] : (~v2_funct_1(X1) & r1_tarski(k2_relat_1(X1),k1_relat_1(sK2)) & v2_funct_1(k5_relat_1(X1,sK2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (~v2_funct_1(sK3) & r1_tarski(k2_relat_1(sK3),k1_relat_1(sK2)) & v2_funct_1(k5_relat_1(sK3,sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (~v2_funct_1(X1) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f7])).
% 0.22/0.55  fof(f7,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : ((~v2_funct_1(X1) & (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,negated_conjecture,(
% 0.22/0.55    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 0.22/0.55    inference(negated_conjecture,[],[f5])).
% 0.22/0.55  fof(f5,conjecture,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).
% 0.22/0.55  fof(f261,plain,(
% 0.22/0.55    v2_funct_1(sK3) | ~spl6_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f260,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    v1_funct_1(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f260,plain,(
% 0.22/0.55    ~v1_funct_1(sK3) | v2_funct_1(sK3) | ~spl6_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f259,f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    v1_relat_1(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f259,plain,(
% 0.22/0.55    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | v2_funct_1(sK3) | ~spl6_2),
% 0.22/0.55    inference(resolution,[],[f206,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X0] : (~sP0(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.55    inference(resolution,[],[f43,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(definition_folding,[],[f12,f18,f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.22/0.55  fof(f206,plain,(
% 0.22/0.55    sP0(sK3) | ~spl6_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f204])).
% 0.22/0.55  fof(f204,plain,(
% 0.22/0.55    spl6_2 <=> sP0(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.55  fof(f258,plain,(
% 0.22/0.55    spl6_4),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f257])).
% 0.22/0.55  fof(f257,plain,(
% 0.22/0.55    $false | spl6_4),
% 0.22/0.55    inference(subsumption_resolution,[],[f256,f30])).
% 0.22/0.55  fof(f256,plain,(
% 0.22/0.55    ~v1_relat_1(sK3) | spl6_4),
% 0.22/0.55    inference(subsumption_resolution,[],[f255,f31])).
% 0.22/0.55  fof(f255,plain,(
% 0.22/0.55    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_4),
% 0.22/0.55    inference(subsumption_resolution,[],[f254,f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    v1_relat_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f254,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_4),
% 0.22/0.55    inference(subsumption_resolution,[],[f253,f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f253,plain,(
% 0.22/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_4),
% 0.22/0.55    inference(resolution,[],[f245,f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f13])).
% 0.22/0.55  % (27557)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.22/0.57  fof(f245,plain,(
% 0.22/0.57    ~v1_relat_1(k5_relat_1(sK3,sK2)) | spl6_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f243])).
% 0.22/0.57  fof(f243,plain,(
% 0.22/0.57    spl6_4 <=> v1_relat_1(k5_relat_1(sK3,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.57  fof(f252,plain,(
% 0.22/0.57    spl6_3),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f251])).
% 0.22/0.57  fof(f251,plain,(
% 0.22/0.57    $false | spl6_3),
% 0.22/0.57    inference(subsumption_resolution,[],[f250,f30])).
% 0.22/0.57  fof(f250,plain,(
% 0.22/0.57    ~v1_relat_1(sK3) | spl6_3),
% 0.22/0.57    inference(subsumption_resolution,[],[f249,f31])).
% 0.22/0.57  fof(f249,plain,(
% 0.22/0.57    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_3),
% 0.22/0.57    inference(subsumption_resolution,[],[f248,f28])).
% 0.22/0.57  fof(f248,plain,(
% 0.22/0.57    ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_3),
% 0.22/0.57    inference(subsumption_resolution,[],[f247,f29])).
% 0.22/0.57  fof(f247,plain,(
% 0.22/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_3),
% 0.22/0.57    inference(resolution,[],[f241,f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f241,plain,(
% 0.22/0.57    ~v1_funct_1(k5_relat_1(sK3,sK2)) | spl6_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f239])).
% 0.22/0.57  fof(f239,plain,(
% 0.22/0.57    spl6_3 <=> v1_funct_1(k5_relat_1(sK3,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.57  fof(f246,plain,(
% 0.22/0.57    ~spl6_3 | ~spl6_4 | spl6_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f237,f200,f243,f239])).
% 0.22/0.57  fof(f200,plain,(
% 0.22/0.57    spl6_1 <=> sP0(k5_relat_1(sK3,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.57  fof(f237,plain,(
% 0.22/0.57    ~v1_relat_1(k5_relat_1(sK3,sK2)) | ~v1_funct_1(k5_relat_1(sK3,sK2)) | spl6_1),
% 0.22/0.57    inference(subsumption_resolution,[],[f236,f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    v2_funct_1(k5_relat_1(sK3,sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f236,plain,(
% 0.22/0.57    ~v1_relat_1(k5_relat_1(sK3,sK2)) | ~v2_funct_1(k5_relat_1(sK3,sK2)) | ~v1_funct_1(k5_relat_1(sK3,sK2)) | spl6_1),
% 0.22/0.57    inference(resolution,[],[f202,f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ( ! [X1] : (sP0(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 0.22/0.57    inference(resolution,[],[f43,f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X0] : (~sP1(X0) | ~v2_funct_1(X0) | sP0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f202,plain,(
% 0.22/0.57    ~sP0(k5_relat_1(sK3,sK2)) | spl6_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f200])).
% 0.22/0.57  fof(f207,plain,(
% 0.22/0.57    ~spl6_1 | spl6_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f198,f204,f200])).
% 0.22/0.57  fof(f198,plain,(
% 0.22/0.57    sP0(sK3) | ~sP0(k5_relat_1(sK3,sK2))),
% 0.22/0.57    inference(subsumption_resolution,[],[f197,f30])).
% 0.22/0.57  fof(f197,plain,(
% 0.22/0.57    ~v1_relat_1(sK3) | sP0(sK3) | ~sP0(k5_relat_1(sK3,sK2))),
% 0.22/0.57    inference(subsumption_resolution,[],[f196,f31])).
% 0.22/0.57  fof(f196,plain,(
% 0.22/0.57    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sP0(sK3) | ~sP0(k5_relat_1(sK3,sK2))),
% 0.22/0.57    inference(subsumption_resolution,[],[f195,f28])).
% 0.22/0.57  fof(f195,plain,(
% 0.22/0.57    ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sP0(sK3) | ~sP0(k5_relat_1(sK3,sK2))),
% 0.22/0.57    inference(subsumption_resolution,[],[f193,f29])).
% 0.22/0.57  fof(f193,plain,(
% 0.22/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sP0(sK3) | ~sP0(k5_relat_1(sK3,sK2))),
% 0.22/0.57    inference(resolution,[],[f192,f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f192,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP0(X0) | ~sP0(k5_relat_1(X0,X1))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f191,f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0] : ((sP0(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.57    inference(rectify,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.57    inference(nnf_transformation,[],[f17])).
% 0.22/0.57  fof(f191,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(X0),k1_relat_1(X0)) | ~sP0(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP0(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f190,f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f190,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(X0),k1_relat_1(X0)) | ~r2_hidden(sK4(X0),k1_relat_1(X0)) | ~sP0(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP0(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) )),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f189])).
% 0.22/0.57  fof(f189,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(X0),k1_relat_1(X0)) | ~r2_hidden(sK4(X0),k1_relat_1(X0)) | ~sP0(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP0(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(superposition,[],[f188,f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f9])).
% 0.22/0.57  fof(f9,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.57  fof(f188,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1))) | ~r2_hidden(sK4(X0),k1_relat_1(k5_relat_1(X0,X1))) | ~sP0(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP0(X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f187,f39])).
% 0.22/0.57  fof(f187,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1))) | ~r2_hidden(sK4(X0),k1_relat_1(k5_relat_1(X0,X1))) | ~sP0(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP0(X0) | ~r2_hidden(sK4(X0),k1_relat_1(X0))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f167,f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X0] : (sK4(X0) != sK5(X0) | sP0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f167,plain,(
% 0.22/0.57    ( ! [X0,X1] : (sK4(X0) = sK5(X0) | ~r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1))) | ~r2_hidden(sK4(X0),k1_relat_1(k5_relat_1(X0,X1))) | ~sP0(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP0(X0) | ~r2_hidden(sK4(X0),k1_relat_1(X0))) )),
% 0.22/0.57    inference(equality_resolution,[],[f115])).
% 0.22/0.57  fof(f115,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(X0,X2)) != k1_funct_1(X1,k1_funct_1(X0,sK4(X0))) | sK5(X0) = X2 | ~r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1))) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) | ~sP0(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP0(X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f106])).
% 0.22/0.57  fof(f106,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(X0,X2)) != k1_funct_1(X1,k1_funct_1(X0,sK4(X0))) | sK5(X0) = X2 | ~r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1))) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) | ~sP0(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP0(X0) | ~r2_hidden(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(superposition,[],[f80,f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(flattening,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X0,X1),X2) != k1_funct_1(X1,k1_funct_1(X0,sK4(X0))) | sK5(X0) = X2 | ~r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1))) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) | ~sP0(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP0(X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f71,f40])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X0,X1),X2) != k1_funct_1(X1,k1_funct_1(X0,sK4(X0))) | sK5(X0) = X2 | ~r2_hidden(sK5(X0),k1_relat_1(k5_relat_1(X0,X1))) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) | ~sP0(k5_relat_1(X0,X1)) | ~r2_hidden(sK5(X0),k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP0(X0)) )),
% 0.22/0.57    inference(superposition,[],[f61,f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X0] : (k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | sP0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ( ! [X4,X2,X5,X3] : (k1_funct_1(X3,k1_funct_1(X2,X4)) != k1_funct_1(k5_relat_1(X2,X3),X5) | X4 = X5 | ~r2_hidden(X4,k1_relat_1(k5_relat_1(X2,X3))) | ~r2_hidden(X5,k1_relat_1(k5_relat_1(X2,X3))) | ~sP0(k5_relat_1(X2,X3)) | ~r2_hidden(X4,k1_relat_1(X2)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.57    inference(superposition,[],[f38,f46])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~sP0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (27536)------------------------------
% 0.22/0.57  % (27536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (27536)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (27536)Memory used [KB]: 6396
% 0.22/0.57  % (27536)Time elapsed: 0.140 s
% 0.22/0.57  % (27536)------------------------------
% 0.22/0.57  % (27536)------------------------------
% 0.22/0.57  % (27531)Success in time 0.21 s
%------------------------------------------------------------------------------
