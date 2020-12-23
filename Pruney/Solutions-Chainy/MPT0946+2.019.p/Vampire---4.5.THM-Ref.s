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
% DateTime   : Thu Dec  3 13:00:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 343 expanded)
%              Number of leaves         :   37 ( 138 expanded)
%              Depth                    :   15
%              Number of atoms          :  680 (1330 expanded)
%              Number of equality atoms :  128 ( 251 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f387,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f101,f105,f109,f132,f157,f177,f192,f200,f216,f230,f241,f243,f260,f264,f283,f305,f313,f366,f369,f374,f386])).

fof(f386,plain,
    ( ~ spl5_4
    | ~ spl5_7
    | ~ spl5_2
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f385,f262,f175,f99,f136,f107])).

fof(f107,plain,
    ( spl5_4
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f136,plain,
    ( spl5_7
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f99,plain,
    ( spl5_2
  <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f175,plain,
    ( spl5_15
  <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f262,plain,
    ( spl5_27
  <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f385,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f381,f263])).

fof(f263,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f262])).

fof(f381,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl5_15 ),
    inference(superposition,[],[f203,f176])).

fof(f176,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(global_subsumption,[],[f57,f202])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f201,f113])).

fof(f113,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f57,f93])).

fof(f93,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f49,f50])).

fof(f50,plain,(
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

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f58,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f374,plain,
    ( spl5_1
    | ~ spl5_3
    | spl5_14
    | ~ spl5_4
    | spl5_7 ),
    inference(avatar_split_clause,[],[f331,f136,f107,f172,f103,f95])).

fof(f95,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f103,plain,
    ( spl5_3
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f172,plain,
    ( spl5_14
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f331,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ spl5_4
    | spl5_7 ),
    inference(resolution,[],[f312,f116])).

fof(f116,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK0)
        | r2_hidden(sK0,X1)
        | ~ v3_ordinal1(X1)
        | sK0 = X1 )
    | ~ spl5_4 ),
    inference(resolution,[],[f69,f108])).

fof(f108,plain,
    ( v3_ordinal1(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f312,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f369,plain,
    ( ~ spl5_22
    | ~ spl5_9
    | ~ spl5_2
    | spl5_35 ),
    inference(avatar_split_clause,[],[f367,f364,f99,f146,f234])).

fof(f234,plain,
    ( spl5_22
  <=> v1_relat_1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f146,plain,
    ( spl5_9
  <=> v1_relat_1(k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f364,plain,
    ( spl5_35
  <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f367,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_35 ),
    inference(resolution,[],[f365,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f365,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | spl5_35 ),
    inference(avatar_component_clause,[],[f364])).

fof(f366,plain,
    ( ~ spl5_3
    | ~ spl5_14
    | ~ spl5_35
    | ~ spl5_8
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f361,f214,f140,f364,f172,f103])).

fof(f140,plain,
    ( spl5_8
  <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f214,plain,
    ( spl5_20
  <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f361,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl5_8
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f359,f215])).

fof(f215,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f214])).

fof(f359,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl5_8 ),
    inference(superposition,[],[f203,f141])).

fof(f141,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f313,plain,
    ( ~ spl5_7
    | spl5_19
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f307,f225,f210,f136])).

fof(f210,plain,
    ( spl5_19
  <=> r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f225,plain,
    ( spl5_21
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f307,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl5_19
    | ~ spl5_21 ),
    inference(resolution,[],[f226,f240])).

fof(f240,plain,
    ( ~ r2_hidden(sK1,sK1)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f210])).

fof(f226,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f225])).

fof(f305,plain,
    ( ~ spl5_9
    | spl5_21
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f304,f281,f225,f146])).

fof(f281,plain,
    ( spl5_28
  <=> sK0 = k3_relat_1(k2_wellord1(k1_wellord2(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f304,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(k1_wellord2(sK1)) )
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f302,f113])).

fof(f302,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,k3_relat_1(k1_wellord2(sK1)))
        | ~ v1_relat_1(k1_wellord2(sK1)) )
    | ~ spl5_28 ),
    inference(superposition,[],[f81,f282])).

fof(f282,plain,
    ( sK0 = k3_relat_1(k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f281])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

fof(f283,plain,
    ( spl5_28
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f277,f140,f103,f281])).

fof(f277,plain,
    ( sK0 = k3_relat_1(k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(superposition,[],[f275,f141])).

fof(f275,plain,
    ( ! [X0] : k1_wellord1(k1_wellord2(sK1),X0) = k3_relat_1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))
    | ~ spl5_3 ),
    inference(resolution,[],[f159,f104])).

fof(f104,plain,
    ( v3_ordinal1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(X0),X1) = k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) ) ),
    inference(global_subsumption,[],[f57,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X0),X1) = k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f70,f66])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X1)
      | k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).

fof(f264,plain,
    ( spl5_27
    | spl5_14
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f253,f198,f103,f172,f262])).

fof(f198,plain,
    ( spl5_17
  <=> ! [X1] :
        ( ~ v3_ordinal1(X1)
        | r2_hidden(sK0,X1)
        | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f253,plain,
    ( r2_hidden(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(resolution,[],[f199,f104])).

fof(f199,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | r2_hidden(sK0,X1)
        | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK0),X1) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f198])).

fof(f260,plain,
    ( ~ spl5_4
    | ~ spl5_3
    | spl5_8
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f178,f172,f140,f103,f107])).

fof(f178,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f173,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

fof(f173,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f243,plain,(
    spl5_22 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl5_22 ),
    inference(resolution,[],[f235,f57])).

fof(f235,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f234])).

fof(f241,plain,
    ( ~ spl5_22
    | ~ spl5_19
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f232,f175,f210,f234])).

fof(f232,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_15 ),
    inference(superposition,[],[f86,f176])).

fof(f86,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
                | sK2(X0,X1,X2) = X1
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
                  & sK2(X0,X1,X2) != X1 )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
          | sK2(X0,X1,X2) = X1
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
            & sK2(X0,X1,X2) != X1 )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f230,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_15
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f229,f136,f175,f107,f103])).

fof(f229,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f137,f68])).

fof(f137,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f216,plain,
    ( spl5_20
    | spl5_7
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f205,f190,f107,f136,f214])).

fof(f190,plain,
    ( spl5_16
  <=> ! [X1] :
        ( ~ v3_ordinal1(X1)
        | r2_hidden(sK1,X1)
        | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f205,plain,
    ( r2_hidden(sK1,sK0)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(resolution,[],[f191,f108])).

fof(f191,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | r2_hidden(sK1,X1)
        | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK1),X1) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f200,plain,
    ( ~ spl5_4
    | spl5_17
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f195,f107,f198,f107])).

fof(f195,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK0),X1)
        | r2_hidden(sK0,X1)
        | ~ v3_ordinal1(sK0) )
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK0),X1)
        | r2_hidden(sK0,X1)
        | ~ v3_ordinal1(sK0)
        | ~ v3_ordinal1(X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f184,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f184,plain,
    ( ! [X1] :
        ( ~ r1_ordinal1(X1,sK0)
        | ~ v3_ordinal1(X1)
        | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK0),X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f114,f108])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(resolution,[],[f79,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f192,plain,
    ( ~ spl5_3
    | spl5_16
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f187,f103,f190,f103])).

fof(f187,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK1),X1)
        | r2_hidden(sK1,X1)
        | ~ v3_ordinal1(sK1) )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK1),X1)
        | r2_hidden(sK1,X1)
        | ~ v3_ordinal1(sK1)
        | ~ v3_ordinal1(X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f183,f67])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ r1_ordinal1(X0,sK1)
        | ~ v3_ordinal1(X0)
        | k1_wellord2(X0) = k2_wellord1(k1_wellord2(sK1),X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f114,f104])).

fof(f177,plain,
    ( spl5_14
    | spl5_1
    | spl5_15
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f169,f130,f103,f175,f95,f172])).

fof(f130,plain,
    ( spl5_6
  <=> ! [X0] :
        ( r2_hidden(sK0,X0)
        | k1_wellord1(k1_wellord2(sK0),X0) = X0
        | sK0 = X0
        | ~ v3_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f169,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(resolution,[],[f131,f104])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK0),X0) = X0
        | sK0 = X0
        | r2_hidden(sK0,X0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f157,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl5_9 ),
    inference(resolution,[],[f147,f57])).

fof(f147,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f132,plain,
    ( ~ spl5_4
    | spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f127,f107,f130,f107])).

fof(f127,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | ~ v3_ordinal1(X0)
        | sK0 = X0
        | k1_wellord1(k1_wellord2(sK0),X0) = X0
        | ~ v3_ordinal1(sK0) )
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | ~ v3_ordinal1(X0)
        | sK0 = X0
        | k1_wellord1(k1_wellord2(sK0),X0) = X0
        | ~ v3_ordinal1(sK0)
        | ~ v3_ordinal1(X0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f116,f68])).

fof(f109,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f53,f107])).

fof(f53,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( sK0 != sK1
    & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK0 != sK1
      & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(f105,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f54,f103])).

fof(f54,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f55,f99])).

fof(f55,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f56,f95])).

fof(f56,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:51:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (5076)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (5068)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (5061)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (5076)Refutation not found, incomplete strategy% (5076)------------------------------
% 0.21/0.50  % (5076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5076)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5076)Memory used [KB]: 6268
% 0.21/0.50  % (5076)Time elapsed: 0.021 s
% 0.21/0.50  % (5076)------------------------------
% 0.21/0.50  % (5076)------------------------------
% 0.21/0.50  % (5081)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (5081)Refutation not found, incomplete strategy% (5081)------------------------------
% 0.21/0.51  % (5081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5081)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5081)Memory used [KB]: 10618
% 0.21/0.51  % (5081)Time elapsed: 0.074 s
% 0.21/0.51  % (5081)------------------------------
% 0.21/0.51  % (5081)------------------------------
% 0.21/0.51  % (5066)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (5073)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (5067)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (5065)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (5063)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (5061)Refutation not found, incomplete strategy% (5061)------------------------------
% 0.21/0.52  % (5061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5061)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5061)Memory used [KB]: 6396
% 0.21/0.52  % (5061)Time elapsed: 0.094 s
% 0.21/0.52  % (5061)------------------------------
% 0.21/0.52  % (5061)------------------------------
% 0.21/0.52  % (5062)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (5062)Refutation not found, incomplete strategy% (5062)------------------------------
% 0.21/0.52  % (5062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5062)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5062)Memory used [KB]: 10618
% 0.21/0.52  % (5062)Time elapsed: 0.097 s
% 0.21/0.52  % (5062)------------------------------
% 0.21/0.52  % (5062)------------------------------
% 0.21/0.52  % (5075)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (5064)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (5074)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (5069)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (5074)Refutation not found, incomplete strategy% (5074)------------------------------
% 0.21/0.52  % (5074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5074)Memory used [KB]: 1663
% 0.21/0.52  % (5074)Time elapsed: 0.098 s
% 0.21/0.52  % (5074)------------------------------
% 0.21/0.52  % (5074)------------------------------
% 0.21/0.53  % (5080)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (5077)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.54  % (5078)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.54  % (5067)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f387,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f97,f101,f105,f109,f132,f157,f177,f192,f200,f216,f230,f241,f243,f260,f264,f283,f305,f313,f366,f369,f374,f386])).
% 0.21/0.54  fof(f386,plain,(
% 0.21/0.54    ~spl5_4 | ~spl5_7 | ~spl5_2 | ~spl5_15 | ~spl5_27),
% 0.21/0.54    inference(avatar_split_clause,[],[f385,f262,f175,f99,f136,f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    spl5_4 <=> v3_ordinal1(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl5_7 <=> r2_hidden(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl5_2 <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    spl5_15 <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.54  fof(f262,plain,(
% 0.21/0.54    spl5_27 <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.54  fof(f385,plain,(
% 0.21/0.54    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | (~spl5_15 | ~spl5_27)),
% 0.21/0.54    inference(forward_demodulation,[],[f381,f263])).
% 0.21/0.54  fof(f263,plain,(
% 0.21/0.54    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl5_27),
% 0.21/0.54    inference(avatar_component_clause,[],[f262])).
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~spl5_15),
% 0.21/0.54    inference(superposition,[],[f203,f176])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~spl5_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f175])).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 0.21/0.54    inference(global_subsumption,[],[f57,f202])).
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f201,f113])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.54    inference(global_subsumption,[],[f57,f93])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.54    inference(equality_resolution,[],[f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f49,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(rectify,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.21/0.54    inference(resolution,[],[f58,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v2_wellord1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.54  fof(f374,plain,(
% 0.21/0.54    spl5_1 | ~spl5_3 | spl5_14 | ~spl5_4 | spl5_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f331,f136,f107,f172,f103,f95])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    spl5_1 <=> sK0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    spl5_3 <=> v3_ordinal1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    spl5_14 <=> r2_hidden(sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.54  fof(f331,plain,(
% 0.21/0.54    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | sK0 = sK1 | (~spl5_4 | spl5_7)),
% 0.21/0.54    inference(resolution,[],[f312,f116])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(X1,sK0) | r2_hidden(sK0,X1) | ~v3_ordinal1(X1) | sK0 = X1) ) | ~spl5_4),
% 0.21/0.54    inference(resolution,[],[f69,f108])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    v3_ordinal1(sK0) | ~spl5_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f107])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.54  fof(f312,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK0) | spl5_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f136])).
% 0.21/0.54  fof(f369,plain,(
% 0.21/0.54    ~spl5_22 | ~spl5_9 | ~spl5_2 | spl5_35),
% 0.21/0.54    inference(avatar_split_clause,[],[f367,f364,f99,f146,f234])).
% 0.21/0.54  fof(f234,plain,(
% 0.21/0.54    spl5_22 <=> v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    spl5_9 <=> v1_relat_1(k1_wellord2(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.54  fof(f364,plain,(
% 0.21/0.54    spl5_35 <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.54  fof(f367,plain,(
% 0.21/0.54    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK0)) | spl5_35),
% 0.21/0.54    inference(resolution,[],[f365,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).
% 0.21/0.54  fof(f365,plain,(
% 0.21/0.54    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | spl5_35),
% 0.21/0.54    inference(avatar_component_clause,[],[f364])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    ~spl5_3 | ~spl5_14 | ~spl5_35 | ~spl5_8 | ~spl5_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f361,f214,f140,f364,f172,f103])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    spl5_8 <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    spl5_20 <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | (~spl5_8 | ~spl5_20)),
% 0.21/0.54    inference(forward_demodulation,[],[f359,f215])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl5_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f214])).
% 0.21/0.54  fof(f359,plain,(
% 0.21/0.54    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~spl5_8),
% 0.21/0.54    inference(superposition,[],[f203,f141])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~spl5_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f140])).
% 0.21/0.54  fof(f313,plain,(
% 0.21/0.54    ~spl5_7 | spl5_19 | ~spl5_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f307,f225,f210,f136])).
% 0.21/0.54  fof(f210,plain,(
% 0.21/0.54    spl5_19 <=> r2_hidden(sK1,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    spl5_21 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK0) | (spl5_19 | ~spl5_21)),
% 0.21/0.54    inference(resolution,[],[f226,f240])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK1) | spl5_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f210])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl5_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f225])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    ~spl5_9 | spl5_21 | ~spl5_28),
% 0.21/0.54    inference(avatar_split_clause,[],[f304,f281,f225,f146])).
% 0.21/0.54  fof(f281,plain,(
% 0.21/0.54    spl5_28 <=> sK0 = k3_relat_1(k2_wellord1(k1_wellord2(sK1),sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.54  fof(f304,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | ~v1_relat_1(k1_wellord2(sK1))) ) | ~spl5_28),
% 0.21/0.54    inference(forward_demodulation,[],[f302,f113])).
% 0.21/0.54  fof(f302,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,k3_relat_1(k1_wellord2(sK1))) | ~v1_relat_1(k1_wellord2(sK1))) ) | ~spl5_28),
% 0.21/0.54    inference(superposition,[],[f81,f282])).
% 0.21/0.54  fof(f282,plain,(
% 0.21/0.54    sK0 = k3_relat_1(k2_wellord1(k1_wellord2(sK1),sK0)) | ~spl5_28),
% 0.21/0.54    inference(avatar_component_clause,[],[f281])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | r2_hidden(X0,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).
% 0.21/0.54  fof(f283,plain,(
% 0.21/0.54    spl5_28 | ~spl5_3 | ~spl5_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f277,f140,f103,f281])).
% 0.21/0.54  fof(f277,plain,(
% 0.21/0.54    sK0 = k3_relat_1(k2_wellord1(k1_wellord2(sK1),sK0)) | (~spl5_3 | ~spl5_8)),
% 0.21/0.54    inference(superposition,[],[f275,f141])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    ( ! [X0] : (k1_wellord1(k1_wellord2(sK1),X0) = k3_relat_1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))) ) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f159,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    v3_ordinal1(sK1) | ~spl5_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f103])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(X0),X1) = k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))) )),
% 0.21/0.54    inference(global_subsumption,[],[f57,f158])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X0),X1) = k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v1_relat_1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f70,f66])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v2_wellord1(X1) | k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : (k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    spl5_27 | spl5_14 | ~spl5_3 | ~spl5_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f253,f198,f103,f172,f262])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    spl5_17 <=> ! [X1] : (~v3_ordinal1(X1) | r2_hidden(sK0,X1) | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK0),X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.54  fof(f253,plain,(
% 0.21/0.54    r2_hidden(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | (~spl5_3 | ~spl5_17)),
% 0.21/0.54    inference(resolution,[],[f199,f104])).
% 0.21/0.54  fof(f199,plain,(
% 0.21/0.54    ( ! [X1] : (~v3_ordinal1(X1) | r2_hidden(sK0,X1) | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK0),X1)) ) | ~spl5_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f198])).
% 0.21/0.54  fof(f260,plain,(
% 0.21/0.54    ~spl5_4 | ~spl5_3 | spl5_8 | ~spl5_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f178,f172,f140,f103,f107])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl5_14),
% 0.21/0.54    inference(resolution,[],[f173,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    r2_hidden(sK0,sK1) | ~spl5_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f172])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    spl5_22),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f242])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    $false | spl5_22),
% 0.21/0.54    inference(resolution,[],[f235,f57])).
% 0.21/0.54  fof(f235,plain,(
% 0.21/0.54    ~v1_relat_1(k1_wellord2(sK0)) | spl5_22),
% 0.21/0.54    inference(avatar_component_clause,[],[f234])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    ~spl5_22 | ~spl5_19 | ~spl5_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f232,f175,f210,f234])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK1) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_15),
% 0.21/0.54    inference(superposition,[],[f86,f176])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) | sK2(X0,X1,X2) = X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) & sK2(X0,X1,X2) != X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) | sK2(X0,X1,X2) = X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) & sK2(X0,X1,X2) != X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(rectify,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 0.21/0.54  fof(f230,plain,(
% 0.21/0.54    ~spl5_3 | ~spl5_4 | spl5_15 | ~spl5_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f229,f136,f175,f107,f103])).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~spl5_7),
% 0.21/0.54    inference(resolution,[],[f137,f68])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    r2_hidden(sK1,sK0) | ~spl5_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f136])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    spl5_20 | spl5_7 | ~spl5_4 | ~spl5_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f205,f190,f107,f136,f214])).
% 0.21/0.54  fof(f190,plain,(
% 0.21/0.54    spl5_16 <=> ! [X1] : (~v3_ordinal1(X1) | r2_hidden(sK1,X1) | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK1),X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.54  fof(f205,plain,(
% 0.21/0.54    r2_hidden(sK1,sK0) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | (~spl5_4 | ~spl5_16)),
% 0.21/0.54    inference(resolution,[],[f191,f108])).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    ( ! [X1] : (~v3_ordinal1(X1) | r2_hidden(sK1,X1) | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK1),X1)) ) | ~spl5_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f190])).
% 0.21/0.54  fof(f200,plain,(
% 0.21/0.54    ~spl5_4 | spl5_17 | ~spl5_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f195,f107,f198,f107])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    ( ! [X1] : (~v3_ordinal1(X1) | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK0),X1) | r2_hidden(sK0,X1) | ~v3_ordinal1(sK0)) ) | ~spl5_4),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f194])).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    ( ! [X1] : (~v3_ordinal1(X1) | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK0),X1) | r2_hidden(sK0,X1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(X1)) ) | ~spl5_4),
% 0.21/0.54    inference(resolution,[],[f184,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    ( ! [X1] : (~r1_ordinal1(X1,sK0) | ~v3_ordinal1(X1) | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK0),X1)) ) | ~spl5_4),
% 0.21/0.54    inference(resolution,[],[f114,f108])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X0) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.21/0.54    inference(resolution,[],[f79,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.54  fof(f192,plain,(
% 0.21/0.54    ~spl5_3 | spl5_16 | ~spl5_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f187,f103,f190,f103])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    ( ! [X1] : (~v3_ordinal1(X1) | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK1),X1) | r2_hidden(sK1,X1) | ~v3_ordinal1(sK1)) ) | ~spl5_3),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f186])).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    ( ! [X1] : (~v3_ordinal1(X1) | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK1),X1) | r2_hidden(sK1,X1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(X1)) ) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f183,f67])).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_ordinal1(X0,sK1) | ~v3_ordinal1(X0) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(sK1),X0)) ) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f114,f104])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    spl5_14 | spl5_1 | spl5_15 | ~spl5_3 | ~spl5_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f169,f130,f103,f175,f95,f172])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    spl5_6 <=> ! [X0] : (r2_hidden(sK0,X0) | k1_wellord1(k1_wellord2(sK0),X0) = X0 | sK0 = X0 | ~v3_ordinal1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | sK0 = sK1 | r2_hidden(sK0,sK1) | (~spl5_3 | ~spl5_6)),
% 0.21/0.54    inference(resolution,[],[f131,f104])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    ( ! [X0] : (~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK0),X0) = X0 | sK0 = X0 | r2_hidden(sK0,X0)) ) | ~spl5_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f130])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    spl5_9),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    $false | spl5_9),
% 0.21/0.54    inference(resolution,[],[f147,f57])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    ~v1_relat_1(k1_wellord2(sK1)) | spl5_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f146])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ~spl5_4 | spl5_6 | ~spl5_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f127,f107,f130,f107])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK0,X0) | ~v3_ordinal1(X0) | sK0 = X0 | k1_wellord1(k1_wellord2(sK0),X0) = X0 | ~v3_ordinal1(sK0)) ) | ~spl5_4),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f125])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK0,X0) | ~v3_ordinal1(X0) | sK0 = X0 | k1_wellord1(k1_wellord2(sK0),X0) = X0 | ~v3_ordinal1(sK0) | ~v3_ordinal1(X0)) ) | ~spl5_4),
% 0.21/0.54    inference(resolution,[],[f116,f68])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    spl5_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f53,f107])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    v3_ordinal1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f40,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f14])).
% 0.21/0.54  fof(f14,conjecture,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    spl5_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f54,f103])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    v3_ordinal1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    spl5_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f55,f99])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ~spl5_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f56,f95])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    sK0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (5067)------------------------------
% 0.21/0.54  % (5067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5067)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (5067)Memory used [KB]: 10874
% 0.21/0.54  % (5067)Time elapsed: 0.095 s
% 0.21/0.54  % (5067)------------------------------
% 0.21/0.54  % (5067)------------------------------
% 0.21/0.54  % (5072)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.55  % (5064)Refutation not found, incomplete strategy% (5064)------------------------------
% 0.21/0.55  % (5064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5064)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5064)Memory used [KB]: 10874
% 0.21/0.55  % (5064)Time elapsed: 0.105 s
% 0.21/0.55  % (5064)------------------------------
% 0.21/0.55  % (5064)------------------------------
% 0.21/0.55  % (5079)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.55  % (5070)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.55  % (5060)Success in time 0.18 s
%------------------------------------------------------------------------------
