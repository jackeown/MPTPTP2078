%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0636+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 206 expanded)
%              Number of leaves         :   17 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  322 ( 830 expanded)
%              Number of equality atoms :   35 (  76 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f521,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f71,f72,f77,f82,f337,f346,f445,f480,f519])).

fof(f519,plain,
    ( spl8_2
    | ~ spl8_23 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | spl8_2
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f510,f65])).

fof(f65,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK6))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl8_2
  <=> r2_hidden(sK4,k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f510,plain,
    ( r2_hidden(sK4,k1_relat_1(sK6))
    | ~ spl8_23 ),
    inference(resolution,[],[f334,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0))
        | ~ r2_hidden(X1,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X2)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
        & r2_hidden(X0,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f334,plain,
    ( sP2(k6_relat_1(sK5),sK4,sK6)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl8_23
  <=> sP2(k6_relat_1(sK5),sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f480,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | spl8_23 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_3
    | spl8_23 ),
    inference(subsumption_resolution,[],[f478,f68])).

fof(f68,plain,
    ( r2_hidden(k1_funct_1(sK6,sK4),sK5)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl8_3
  <=> r2_hidden(k1_funct_1(sK6,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f478,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
    | ~ spl8_2
    | spl8_23 ),
    inference(forward_demodulation,[],[f470,f106])).

fof(f106,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f103,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK7(X0,X1) != k1_funct_1(X0,sK7(X0,X1))
          & r2_hidden(sK7(X0,X1),X1) )
        | k1_relat_1(X0) != X1 )
      & ( ( ! [X3] :
              ( k1_funct_1(X0,X3) = X3
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != X2
          & r2_hidden(X2,X1) )
     => ( sK7(X0,X1) != k1_funct_1(X0,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( k1_funct_1(X0,X2) != X2
            & r2_hidden(X2,X1) )
        | k1_relat_1(X0) != X1 )
      & ( ( ! [X3] :
              ( k1_funct_1(X0,X3) = X3
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( k1_funct_1(X1,X2) = X2
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f103,plain,(
    ! [X0] : sP0(k6_relat_1(X0),X0) ),
    inference(unit_resulting_resolution,[],[f93,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ sP1(X0,k6_relat_1(X0))
      | sP0(k6_relat_1(X0),X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | k6_relat_1(X0) != X1
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k6_relat_1(X0) != X1 ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f93,plain,(
    ! [X0,X1] : sP1(X0,k6_relat_1(X1)) ),
    inference(unit_resulting_resolution,[],[f39,f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f10,f14,f13])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f41,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f470,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK4),k1_relat_1(k6_relat_1(sK5)))
    | ~ spl8_2
    | spl8_23 ),
    inference(unit_resulting_resolution,[],[f333,f64,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0))
      | sP2(X0,X1,X2)
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,
    ( r2_hidden(sK4,k1_relat_1(sK6))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f333,plain,
    ( ~ sP2(k6_relat_1(sK5),sK4,sK6)
    | spl8_23 ),
    inference(avatar_component_clause,[],[f332])).

fof(f445,plain,
    ( ~ spl8_23
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f426,f79,f74,f59,f332])).

fof(f59,plain,
    ( spl8_1
  <=> r2_hidden(sK4,k1_relat_1(k5_relat_1(sK6,k6_relat_1(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f74,plain,
    ( spl8_4
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f79,plain,
    ( spl8_5
  <=> v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f426,plain,
    ( ~ sP2(k6_relat_1(sK5),sK4,sK6)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f271,f61,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2)))
      | ~ sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2)))
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2))) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ sP2(X1,X0,X2) )
        & ( sP2(X1,X0,X2)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
      | ~ sP3(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      <=> sP2(X1,X0,X2) )
      | ~ sP3(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f61,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(k5_relat_1(sK6,k6_relat_1(sK5))))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f271,plain,
    ( ! [X0,X1] : sP3(sK6,X0,k6_relat_1(X1))
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f39,f41,f81,f76,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP3(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f12,f17,f16])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f76,plain,
    ( v1_funct_1(sK6)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f81,plain,
    ( v1_relat_1(sK6)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f346,plain,
    ( spl8_3
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f342,f332,f67])).

fof(f342,plain,
    ( r2_hidden(k1_funct_1(sK6,sK4),sK5)
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f338,f106])).

fof(f338,plain,
    ( r2_hidden(k1_funct_1(sK6,sK4),k1_relat_1(k6_relat_1(sK5)))
    | ~ spl8_23 ),
    inference(unit_resulting_resolution,[],[f334,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f337,plain,
    ( spl8_23
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f336,f79,f74,f59,f332])).

fof(f336,plain,
    ( sP2(k6_relat_1(sK5),sK4,sK6)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f328,f271])).

fof(f328,plain,
    ( sP2(k6_relat_1(sK5),sK4,sK6)
    | ~ sP3(sK6,sK4,k6_relat_1(sK5))
    | ~ spl8_1 ),
    inference(resolution,[],[f49,f60])).

fof(f60,plain,
    ( r2_hidden(sK4,k1_relat_1(k5_relat_1(sK6,k6_relat_1(sK5))))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2)))
      | sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f34,f79])).

fof(f34,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
      | ~ r2_hidden(sK4,k1_relat_1(sK6))
      | ~ r2_hidden(sK4,k1_relat_1(k5_relat_1(sK6,k6_relat_1(sK5)))) )
    & ( ( r2_hidden(k1_funct_1(sK6,sK4),sK5)
        & r2_hidden(sK4,k1_relat_1(sK6)) )
      | r2_hidden(sK4,k1_relat_1(k5_relat_1(sK6,k6_relat_1(sK5)))) )
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
        | ~ r2_hidden(sK4,k1_relat_1(sK6))
        | ~ r2_hidden(sK4,k1_relat_1(k5_relat_1(sK6,k6_relat_1(sK5)))) )
      & ( ( r2_hidden(k1_funct_1(sK6,sK4),sK5)
          & r2_hidden(sK4,k1_relat_1(sK6)) )
        | r2_hidden(sK4,k1_relat_1(k5_relat_1(sK6,k6_relat_1(sK5)))) )
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

fof(f77,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f36,f63,f59])).

fof(f36,plain,
    ( r2_hidden(sK4,k1_relat_1(sK6))
    | r2_hidden(sK4,k1_relat_1(k5_relat_1(sK6,k6_relat_1(sK5)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f37,f67,f59])).

fof(f37,plain,
    ( r2_hidden(k1_funct_1(sK6,sK4),sK5)
    | r2_hidden(sK4,k1_relat_1(k5_relat_1(sK6,k6_relat_1(sK5)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f38,f67,f63,f59])).

fof(f38,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
    | ~ r2_hidden(sK4,k1_relat_1(sK6))
    | ~ r2_hidden(sK4,k1_relat_1(k5_relat_1(sK6,k6_relat_1(sK5)))) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
