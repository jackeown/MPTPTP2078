%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 315 expanded)
%              Number of leaves         :   21 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          :  437 (1868 expanded)
%              Number of equality atoms :   37 ( 282 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f88,f92,f111,f113,f120,f133,f139,f177,f179,f181])).

fof(f181,plain,
    ( spl5_1
    | spl5_9 ),
    inference(avatar_split_clause,[],[f180,f109,f59])).

fof(f59,plain,
    ( spl5_1
  <=> v6_relat_2(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f109,plain,
    ( spl5_9
  <=> r2_hidden(sK2(k1_wellord2(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f180,plain,
    ( v6_relat_2(k1_wellord2(sK0))
    | spl5_9 ),
    inference(resolution,[],[f110,f72])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_wellord2(X0)),X0)
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(global_subsumption,[],[f33,f71])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_wellord2(X0)),X0)
      | v6_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f36,f68])).

fof(f68,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f33,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f28])).

fof(f28,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k3_relat_1(X0))
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
            & sK1(X0) != sK2(X0)
            & r2_hidden(sK2(X0),k3_relat_1(X0))
            & r2_hidden(sK1(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
        & sK1(X0) != sK2(X0)
        & r2_hidden(sK2(X0),k3_relat_1(X0))
        & r2_hidden(sK1(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f33,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f110,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK0)),sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f179,plain,
    ( spl5_1
    | spl5_8 ),
    inference(avatar_split_clause,[],[f178,f106,f59])).

fof(f106,plain,
    ( spl5_8
  <=> r2_hidden(sK1(k1_wellord2(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f178,plain,
    ( v6_relat_2(k1_wellord2(sK0))
    | spl5_8 ),
    inference(resolution,[],[f107,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_wellord2(X0)),X0)
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(global_subsumption,[],[f33,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_wellord2(X0)),X0)
      | v6_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f35,f68])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k3_relat_1(X0))
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f107,plain,
    ( ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f177,plain,
    ( ~ spl5_5
    | spl5_1
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f174,f90,f106,f109,f131,f124,f59,f97])).

fof(f97,plain,
    ( spl5_5
  <=> v1_relat_1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f124,plain,
    ( spl5_10
  <=> v3_ordinal1(sK1(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f131,plain,
    ( spl5_12
  <=> r1_ordinal1(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f90,plain,
    ( spl5_4
  <=> ! [X3,X2] :
        ( ~ r1_ordinal1(sK2(k1_wellord2(sK0)),X2)
        | ~ r2_hidden(X2,X3)
        | ~ r2_hidden(sK2(k1_wellord2(sK0)),X3)
        | r2_hidden(k4_tarski(sK2(k1_wellord2(sK0)),X2),k1_wellord2(X3))
        | ~ v3_ordinal1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f174,plain,
    ( ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK2(k1_wellord2(sK0)),sK0)
    | ~ r1_ordinal1(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0)))
    | ~ v3_ordinal1(sK1(k1_wellord2(sK0)))
    | v6_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f91,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(sK2(k1_wellord2(sK0)),X2),k1_wellord2(X3))
        | ~ r2_hidden(X2,X3)
        | ~ r2_hidden(sK2(k1_wellord2(sK0)),X3)
        | ~ r1_ordinal1(sK2(k1_wellord2(sK0)),X2)
        | ~ v3_ordinal1(X2) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f139,plain,
    ( spl5_1
    | ~ spl5_2
    | spl5_10 ),
    inference(avatar_split_clause,[],[f136,f124,f63,f59])).

fof(f63,plain,
    ( spl5_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f136,plain,
    ( ~ v3_ordinal1(sK0)
    | v6_relat_2(k1_wellord2(sK0))
    | spl5_10 ),
    inference(resolution,[],[f134,f70])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(k1_wellord2(sK0)),X0)
        | ~ v3_ordinal1(X0) )
    | spl5_10 ),
    inference(resolution,[],[f125,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f125,plain,
    ( ~ v3_ordinal1(sK1(k1_wellord2(sK0)))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f133,plain,
    ( ~ spl5_6
    | ~ spl5_10
    | spl5_12
    | spl5_7 ),
    inference(avatar_split_clause,[],[f122,f103,f131,f124,f100])).

fof(f100,plain,
    ( spl5_6
  <=> v3_ordinal1(sK2(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f103,plain,
    ( spl5_7
  <=> r1_ordinal1(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f122,plain,
    ( r1_ordinal1(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0)))
    | ~ v3_ordinal1(sK1(k1_wellord2(sK0)))
    | ~ v3_ordinal1(sK2(k1_wellord2(sK0)))
    | spl5_7 ),
    inference(resolution,[],[f104,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f104,plain,
    ( ~ r1_ordinal1(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f120,plain,
    ( spl5_1
    | ~ spl5_2
    | spl5_6 ),
    inference(avatar_split_clause,[],[f116,f100,f63,f59])).

fof(f116,plain,
    ( ~ v3_ordinal1(sK0)
    | v6_relat_2(k1_wellord2(sK0))
    | spl5_6 ),
    inference(resolution,[],[f114,f72])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k1_wellord2(sK0)),X0)
        | ~ v3_ordinal1(X0) )
    | spl5_6 ),
    inference(resolution,[],[f101,f47])).

fof(f101,plain,
    ( ~ v3_ordinal1(sK2(k1_wellord2(sK0)))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f113,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f98,f33])).

fof(f98,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f111,plain,
    ( ~ spl5_5
    | spl5_1
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f94,f86,f109,f106,f103,f100,f59,f97])).

fof(f86,plain,
    ( spl5_3
  <=> ! [X1,X0] :
        ( ~ r1_ordinal1(sK1(k1_wellord2(sK0)),X0)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(sK1(k1_wellord2(sK0)),X1)
        | r2_hidden(k4_tarski(sK1(k1_wellord2(sK0)),X0),k1_wellord2(X1))
        | ~ v3_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f94,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK0)),sK0)
    | ~ r2_hidden(sK1(k1_wellord2(sK0)),sK0)
    | ~ r1_ordinal1(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0)))
    | ~ v3_ordinal1(sK2(k1_wellord2(sK0)))
    | v6_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f87,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK0)),X0),k1_wellord2(X1))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(sK1(k1_wellord2(sK0)),X1)
        | ~ r1_ordinal1(sK1(k1_wellord2(sK0)),X0)
        | ~ v3_ordinal1(X0) )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f92,plain,
    ( spl5_1
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f83,f63,f90,f59])).

fof(f83,plain,
    ( ! [X2,X3] :
        ( ~ r1_ordinal1(sK2(k1_wellord2(sK0)),X2)
        | ~ v3_ordinal1(X2)
        | r2_hidden(k4_tarski(sK2(k1_wellord2(sK0)),X2),k1_wellord2(X3))
        | ~ r2_hidden(sK2(k1_wellord2(sK0)),X3)
        | ~ r2_hidden(X2,X3)
        | v6_relat_2(k1_wellord2(sK0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f80,f72])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r1_ordinal1(X0,X2)
        | ~ v3_ordinal1(X2)
        | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f79,f64])).

fof(f64,plain,
    ( v3_ordinal1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f79,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ v3_ordinal1(X5)
      | ~ r2_hidden(X4,X3)
      | ~ r1_ordinal1(X4,X2)
      | ~ v3_ordinal1(X2)
      | r2_hidden(k4_tarski(X4,X2),k1_wellord2(X3))
      | ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f77,f47])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) ) ),
    inference(resolution,[],[f66,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f66,plain,(
    ! [X4,X0,X5] :
      ( ~ r1_tarski(X4,X5)
      | r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(global_subsumption,[],[f33,f55])).

fof(f55,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,
    ( spl5_1
    | spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f82,f63,f86,f59])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r1_ordinal1(sK1(k1_wellord2(sK0)),X0)
        | ~ v3_ordinal1(X0)
        | r2_hidden(k4_tarski(sK1(k1_wellord2(sK0)),X0),k1_wellord2(X1))
        | ~ r2_hidden(sK1(k1_wellord2(sK0)),X1)
        | ~ r2_hidden(X0,X1)
        | v6_relat_2(k1_wellord2(sK0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f80,f70])).

fof(f65,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v6_relat_2(k1_wellord2(sK0))
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ~ v6_relat_2(k1_wellord2(X0))
        & v3_ordinal1(X0) )
   => ( ~ v6_relat_2(k1_wellord2(sK0))
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v6_relat_2(k1_wellord2(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v6_relat_2(k1_wellord2(X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v6_relat_2(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_wellord2)).

fof(f61,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    ~ v6_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:57:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (10921)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (10920)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (10923)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (10929)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (10921)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f61,f65,f88,f92,f111,f113,f120,f133,f139,f177,f179,f181])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    spl5_1 | spl5_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f180,f109,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl5_1 <=> v6_relat_2(k1_wellord2(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl5_9 <=> r2_hidden(sK2(k1_wellord2(sK0)),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    v6_relat_2(k1_wellord2(sK0)) | spl5_9),
% 0.21/0.51    inference(resolution,[],[f110,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK2(k1_wellord2(X0)),X0) | v6_relat_2(k1_wellord2(X0))) )),
% 0.21/0.51    inference(global_subsumption,[],[f33,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK2(k1_wellord2(X0)),X0) | v6_relat_2(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.51    inference(superposition,[],[f36,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.51    inference(global_subsumption,[],[f33,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.51    inference(equality_resolution,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(rectify,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK2(X0),k3_relat_1(X0)) | v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0) & ~r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) & sK1(X0) != sK2(X0) & r2_hidden(sK2(X0),k3_relat_1(X0)) & r2_hidden(sK1(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0) & ~r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) & sK1(X0) != sK2(X0) & r2_hidden(sK2(X0),k3_relat_1(X0)) & r2_hidden(sK1(X0),k3_relat_1(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(rectify,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ~r2_hidden(sK2(k1_wellord2(sK0)),sK0) | spl5_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl5_1 | spl5_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f178,f106,f59])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl5_8 <=> r2_hidden(sK1(k1_wellord2(sK0)),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    v6_relat_2(k1_wellord2(sK0)) | spl5_8),
% 0.21/0.51    inference(resolution,[],[f107,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1(k1_wellord2(X0)),X0) | v6_relat_2(k1_wellord2(X0))) )),
% 0.21/0.51    inference(global_subsumption,[],[f33,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1(k1_wellord2(X0)),X0) | v6_relat_2(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.51    inference(superposition,[],[f35,f68])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1(X0),k3_relat_1(X0)) | v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ~r2_hidden(sK1(k1_wellord2(sK0)),sK0) | spl5_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f106])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ~spl5_5 | spl5_1 | ~spl5_10 | ~spl5_12 | ~spl5_9 | ~spl5_8 | ~spl5_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f174,f90,f106,f109,f131,f124,f59,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl5_5 <=> v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl5_10 <=> v3_ordinal1(sK1(k1_wellord2(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl5_12 <=> r1_ordinal1(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl5_4 <=> ! [X3,X2] : (~r1_ordinal1(sK2(k1_wellord2(sK0)),X2) | ~r2_hidden(X2,X3) | ~r2_hidden(sK2(k1_wellord2(sK0)),X3) | r2_hidden(k4_tarski(sK2(k1_wellord2(sK0)),X2),k1_wellord2(X3)) | ~v3_ordinal1(X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ~r2_hidden(sK1(k1_wellord2(sK0)),sK0) | ~r2_hidden(sK2(k1_wellord2(sK0)),sK0) | ~r1_ordinal1(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0))) | ~v3_ordinal1(sK1(k1_wellord2(sK0))) | v6_relat_2(k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_4),
% 0.21/0.51    inference(resolution,[],[f91,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0) | v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r2_hidden(k4_tarski(sK2(k1_wellord2(sK0)),X2),k1_wellord2(X3)) | ~r2_hidden(X2,X3) | ~r2_hidden(sK2(k1_wellord2(sK0)),X3) | ~r1_ordinal1(sK2(k1_wellord2(sK0)),X2) | ~v3_ordinal1(X2)) ) | ~spl5_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    spl5_1 | ~spl5_2 | spl5_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f136,f124,f63,f59])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    spl5_2 <=> v3_ordinal1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~v3_ordinal1(sK0) | v6_relat_2(k1_wellord2(sK0)) | spl5_10),
% 0.21/0.51    inference(resolution,[],[f134,f70])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK1(k1_wellord2(sK0)),X0) | ~v3_ordinal1(X0)) ) | spl5_10),
% 0.21/0.51    inference(resolution,[],[f125,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ~v3_ordinal1(sK1(k1_wellord2(sK0))) | spl5_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f124])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ~spl5_6 | ~spl5_10 | spl5_12 | spl5_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f122,f103,f131,f124,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl5_6 <=> v3_ordinal1(sK2(k1_wellord2(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl5_7 <=> r1_ordinal1(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    r1_ordinal1(sK2(k1_wellord2(sK0)),sK1(k1_wellord2(sK0))) | ~v3_ordinal1(sK1(k1_wellord2(sK0))) | ~v3_ordinal1(sK2(k1_wellord2(sK0))) | spl5_7),
% 0.21/0.51    inference(resolution,[],[f104,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ~r1_ordinal1(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0))) | spl5_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f103])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl5_1 | ~spl5_2 | spl5_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f116,f100,f63,f59])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ~v3_ordinal1(sK0) | v6_relat_2(k1_wellord2(sK0)) | spl5_6),
% 0.21/0.51    inference(resolution,[],[f114,f72])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK2(k1_wellord2(sK0)),X0) | ~v3_ordinal1(X0)) ) | spl5_6),
% 0.21/0.51    inference(resolution,[],[f101,f47])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ~v3_ordinal1(sK2(k1_wellord2(sK0))) | spl5_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl5_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    $false | spl5_5),
% 0.21/0.51    inference(resolution,[],[f98,f33])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ~v1_relat_1(k1_wellord2(sK0)) | spl5_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ~spl5_5 | spl5_1 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f94,f86,f109,f106,f103,f100,f59,f97])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl5_3 <=> ! [X1,X0] : (~r1_ordinal1(sK1(k1_wellord2(sK0)),X0) | ~r2_hidden(X0,X1) | ~r2_hidden(sK1(k1_wellord2(sK0)),X1) | r2_hidden(k4_tarski(sK1(k1_wellord2(sK0)),X0),k1_wellord2(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ~r2_hidden(sK2(k1_wellord2(sK0)),sK0) | ~r2_hidden(sK1(k1_wellord2(sK0)),sK0) | ~r1_ordinal1(sK1(k1_wellord2(sK0)),sK2(k1_wellord2(sK0))) | ~v3_ordinal1(sK2(k1_wellord2(sK0))) | v6_relat_2(k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_3),
% 0.21/0.51    inference(resolution,[],[f87,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(k1_wellord2(sK0)),X0),k1_wellord2(X1)) | ~r2_hidden(X0,X1) | ~r2_hidden(sK1(k1_wellord2(sK0)),X1) | ~r1_ordinal1(sK1(k1_wellord2(sK0)),X0) | ~v3_ordinal1(X0)) ) | ~spl5_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl5_1 | spl5_4 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f83,f63,f90,f59])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r1_ordinal1(sK2(k1_wellord2(sK0)),X2) | ~v3_ordinal1(X2) | r2_hidden(k4_tarski(sK2(k1_wellord2(sK0)),X2),k1_wellord2(X3)) | ~r2_hidden(sK2(k1_wellord2(sK0)),X3) | ~r2_hidden(X2,X3) | v6_relat_2(k1_wellord2(sK0))) ) | ~spl5_2),
% 0.21/0.51    inference(resolution,[],[f80,f72])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK0) | ~r1_ordinal1(X0,X2) | ~v3_ordinal1(X2) | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,X1)) ) | ~spl5_2),
% 0.21/0.51    inference(resolution,[],[f79,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    v3_ordinal1(sK0) | ~spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f63])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X4,X2,X5,X3] : (~v3_ordinal1(X5) | ~r2_hidden(X4,X3) | ~r1_ordinal1(X4,X2) | ~v3_ordinal1(X2) | r2_hidden(k4_tarski(X4,X2),k1_wellord2(X3)) | ~r2_hidden(X4,X5) | ~r2_hidden(X2,X3)) )),
% 0.21/0.51    inference(resolution,[],[f77,f47])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v3_ordinal1(X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))) )),
% 0.21/0.51    inference(resolution,[],[f66,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X4,X0,X5] : (~r1_tarski(X4,X5) | r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) )),
% 0.21/0.51    inference(global_subsumption,[],[f33,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.51    inference(equality_resolution,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl5_1 | spl5_3 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f82,f63,f86,f59])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_ordinal1(sK1(k1_wellord2(sK0)),X0) | ~v3_ordinal1(X0) | r2_hidden(k4_tarski(sK1(k1_wellord2(sK0)),X0),k1_wellord2(X1)) | ~r2_hidden(sK1(k1_wellord2(sK0)),X1) | ~r2_hidden(X0,X1) | v6_relat_2(k1_wellord2(sK0))) ) | ~spl5_2),
% 0.21/0.51    inference(resolution,[],[f80,f70])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f63])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    v3_ordinal1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ~v6_relat_2(k1_wellord2(sK0)) & v3_ordinal1(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0] : (~v6_relat_2(k1_wellord2(X0)) & v3_ordinal1(X0)) => (~v6_relat_2(k1_wellord2(sK0)) & v3_ordinal1(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0] : (~v6_relat_2(k1_wellord2(X0)) & v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (v3_ordinal1(X0) => v6_relat_2(k1_wellord2(X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => v6_relat_2(k1_wellord2(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_wellord2)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ~spl5_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f59])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ~v6_relat_2(k1_wellord2(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (10921)------------------------------
% 0.21/0.51  % (10921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10921)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (10921)Memory used [KB]: 10746
% 0.21/0.51  % (10921)Time elapsed: 0.060 s
% 0.21/0.51  % (10921)------------------------------
% 0.21/0.51  % (10921)------------------------------
% 0.21/0.52  % (10931)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (10928)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (10914)Success in time 0.151 s
%------------------------------------------------------------------------------
