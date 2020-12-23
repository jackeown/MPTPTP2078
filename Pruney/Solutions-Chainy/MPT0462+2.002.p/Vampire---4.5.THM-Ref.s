%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 471 expanded)
%              Number of leaves         :   36 ( 232 expanded)
%              Depth                    :    8
%              Number of atoms          :  425 (1734 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f58,f63,f68,f81,f86,f91,f96,f101,f106,f111,f116,f129,f134,f139,f144,f149,f154,f159,f164,f171,f176,f183,f188,f192,f193])).

fof(f193,plain,
    ( spl5_27
    | ~ spl5_21
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f189,f173,f151,f185])).

fof(f185,plain,
    ( spl5_27
  <=> r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f151,plain,
    ( spl5_21
  <=> r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f173,plain,
    ( spl5_25
  <=> r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f189,plain,
    ( r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK1,sK2))
    | ~ spl5_21
    | ~ spl5_25 ),
    inference(unit_resulting_resolution,[],[f153,f175,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f175,plain,
    ( r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK0,sK2))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f173])).

fof(f153,plain,
    ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f151])).

fof(f192,plain,
    ( spl5_26
    | ~ spl5_11
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f190,f173,f93,f180])).

fof(f180,plain,
    ( spl5_26
  <=> r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f93,plain,
    ( spl5_11
  <=> r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f190,plain,
    ( r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK0,sK3))
    | ~ spl5_11
    | ~ spl5_25 ),
    inference(unit_resulting_resolution,[],[f95,f175,f31])).

fof(f95,plain,
    ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK0,sK3))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f188,plain,
    ( ~ spl5_27
    | ~ spl5_10
    | spl5_24 ),
    inference(avatar_split_clause,[],[f177,f168,f88,f185])).

fof(f88,plain,
    ( spl5_10
  <=> r1_tarski(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f168,plain,
    ( spl5_24
  <=> r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f177,plain,
    ( ~ r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK1,sK2))
    | ~ spl5_10
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f90,f170,f31])).

fof(f170,plain,
    ( ~ r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK1,sK3))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f168])).

fof(f90,plain,
    ( r1_tarski(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f183,plain,
    ( ~ spl5_26
    | ~ spl5_20
    | spl5_24 ),
    inference(avatar_split_clause,[],[f178,f168,f146,f180])).

fof(f146,plain,
    ( spl5_20
  <=> r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f178,plain,
    ( ~ r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK0,sK3))
    | ~ spl5_20
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f148,f170,f31])).

fof(f148,plain,
    ( r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f146])).

fof(f176,plain,
    ( spl5_25
    | spl5_1 ),
    inference(avatar_split_clause,[],[f165,f35,f173])).

fof(f35,plain,
    ( spl5_1
  <=> r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f165,plain,
    ( r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK0,sK2))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f37,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f171,plain,
    ( ~ spl5_24
    | spl5_1 ),
    inference(avatar_split_clause,[],[f166,f35,f168])).

fof(f166,plain,
    ( ~ r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK1,sK3))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f37,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f164,plain,
    ( spl5_23
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f117,f65,f60,f45,f161])).

fof(f161,plain,
    ( spl5_23
  <=> r1_tarski(k5_relat_1(sK0,sK0),k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f45,plain,
    ( spl5_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f60,plain,
    ( spl5_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f65,plain,
    ( spl5_7
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f117,plain,
    ( r1_tarski(k5_relat_1(sK0,sK0),k5_relat_1(sK1,sK0))
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f67,f67,f62,f47,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).

fof(f47,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f62,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f67,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f159,plain,
    ( spl5_22
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f118,f65,f60,f45,f156])).

fof(f156,plain,
    ( spl5_22
  <=> r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f118,plain,
    ( r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK1,sK1))
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f62,f67,f62,f47,f30])).

fof(f154,plain,
    ( spl5_21
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f119,f65,f60,f55,f45,f151])).

fof(f55,plain,
    ( spl5_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f119,plain,
    ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f57,f67,f62,f47,f30])).

fof(f57,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f149,plain,
    ( spl5_20
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f120,f65,f60,f50,f45,f146])).

fof(f50,plain,
    ( spl5_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f120,plain,
    ( r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f52,f67,f62,f47,f30])).

fof(f52,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f144,plain,
    ( spl5_19
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f121,f65,f60,f45,f141])).

fof(f141,plain,
    ( spl5_19
  <=> r1_tarski(k5_relat_1(sK0,sK0),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f121,plain,
    ( r1_tarski(k5_relat_1(sK0,sK0),k5_relat_1(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f67,f67,f62,f47,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f139,plain,
    ( spl5_18
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f122,f65,f60,f45,f136])).

fof(f136,plain,
    ( spl5_18
  <=> r1_tarski(k5_relat_1(sK1,sK0),k5_relat_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f122,plain,
    ( r1_tarski(k5_relat_1(sK1,sK0),k5_relat_1(sK1,sK1))
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f62,f67,f62,f47,f29])).

fof(f134,plain,
    ( spl5_17
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f123,f65,f60,f55,f45,f131])).

fof(f131,plain,
    ( spl5_17
  <=> r1_tarski(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f123,plain,
    ( r1_tarski(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f57,f67,f62,f47,f29])).

fof(f129,plain,
    ( spl5_16
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f124,f65,f60,f50,f45,f126])).

fof(f126,plain,
    ( spl5_16
  <=> r1_tarski(k5_relat_1(sK3,sK0),k5_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f124,plain,
    ( r1_tarski(k5_relat_1(sK3,sK0),k5_relat_1(sK3,sK1))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f52,f67,f62,f47,f29])).

fof(f116,plain,
    ( spl5_15
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f69,f65,f55,f50,f40,f113])).

fof(f113,plain,
    ( spl5_15
  <=> r1_tarski(k5_relat_1(sK2,sK0),k5_relat_1(sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f40,plain,
    ( spl5_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f69,plain,
    ( r1_tarski(k5_relat_1(sK2,sK0),k5_relat_1(sK3,sK0))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f67,f57,f52,f42,f30])).

fof(f42,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f111,plain,
    ( spl5_14
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f70,f60,f55,f50,f40,f108])).

fof(f108,plain,
    ( spl5_14
  <=> r1_tarski(k5_relat_1(sK2,sK1),k5_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f70,plain,
    ( r1_tarski(k5_relat_1(sK2,sK1),k5_relat_1(sK3,sK1))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f62,f57,f52,f42,f30])).

fof(f106,plain,
    ( spl5_13
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f71,f55,f50,f40,f103])).

fof(f103,plain,
    ( spl5_13
  <=> r1_tarski(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f71,plain,
    ( r1_tarski(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f57,f57,f52,f42,f30])).

fof(f101,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f72,f55,f50,f40,f98])).

fof(f98,plain,
    ( spl5_12
  <=> r1_tarski(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f72,plain,
    ( r1_tarski(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f52,f57,f52,f42,f30])).

fof(f96,plain,
    ( spl5_11
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f73,f65,f55,f50,f40,f93])).

fof(f73,plain,
    ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK0,sK3))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f67,f57,f52,f42,f29])).

fof(f91,plain,
    ( spl5_10
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f74,f60,f55,f50,f40,f88])).

fof(f74,plain,
    ( r1_tarski(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f62,f57,f52,f42,f29])).

fof(f86,plain,
    ( spl5_9
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f75,f55,f50,f40,f83])).

fof(f83,plain,
    ( spl5_9
  <=> r1_tarski(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f75,plain,
    ( r1_tarski(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f57,f57,f52,f42,f29])).

fof(f81,plain,
    ( spl5_8
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f76,f55,f50,f40,f78])).

fof(f78,plain,
    ( spl5_8
  <=> r1_tarski(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f76,plain,
    ( r1_tarski(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f52,f57,f52,f42,f29])).

fof(f68,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f22,f65])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                    & r1_tarski(X2,X3)
                    & r1_tarski(X0,X1)
                    & v1_relat_1(X3) )
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(sK0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                & r1_tarski(X2,X3)
                & r1_tarski(sK0,X1)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3))
              & r1_tarski(X2,X3)
              & r1_tarski(sK0,sK1)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3))
            & r1_tarski(X2,X3)
            & r1_tarski(sK0,sK1)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3))
          & r1_tarski(sK2,X3)
          & r1_tarski(sK0,sK1)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3))
        & r1_tarski(sK2,X3)
        & r1_tarski(sK0,sK1)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ! [X3] :
                    ( v1_relat_1(X3)
                   => ( ( r1_tarski(X2,X3)
                        & r1_tarski(X0,X1) )
                     => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

fof(f63,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f23,f60])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f26,f45])).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f27,f40])).

fof(f27,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f28,f35])).

fof(f28,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (31255)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  % (31255)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f58,f63,f68,f81,f86,f91,f96,f101,f106,f111,f116,f129,f134,f139,f144,f149,f154,f159,f164,f171,f176,f183,f188,f192,f193])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    spl5_27 | ~spl5_21 | ~spl5_25),
% 0.21/0.48    inference(avatar_split_clause,[],[f189,f173,f151,f185])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    spl5_27 <=> r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    spl5_21 <=> r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    spl5_25 <=> r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK1,sK2)) | (~spl5_21 | ~spl5_25)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f153,f175,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK0,sK2)) | ~spl5_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f173])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) | ~spl5_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f151])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    spl5_26 | ~spl5_11 | ~spl5_25),
% 0.21/0.48    inference(avatar_split_clause,[],[f190,f173,f93,f180])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    spl5_26 <=> r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK0,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl5_11 <=> r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK0,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK0,sK3)) | (~spl5_11 | ~spl5_25)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f95,f175,f31])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK0,sK3)) | ~spl5_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f93])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ~spl5_27 | ~spl5_10 | spl5_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f177,f168,f88,f185])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl5_10 <=> r1_tarski(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    spl5_24 <=> r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK1,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ~r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK1,sK2)) | (~spl5_10 | spl5_24)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f90,f170,f31])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ~r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK1,sK3)) | spl5_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f168])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3)) | ~spl5_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    ~spl5_26 | ~spl5_20 | spl5_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f178,f168,f146,f180])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    spl5_20 <=> r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ~r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK0,sK3)) | (~spl5_20 | spl5_24)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f148,f170,f31])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3)) | ~spl5_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f146])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    spl5_25 | spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f165,f35,f173])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    spl5_1 <=> r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK0,sK2)) | spl5_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f37,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) | spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f35])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    ~spl5_24 | spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f166,f35,f168])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    ~r2_hidden(sK4(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)),k5_relat_1(sK1,sK3)) | spl5_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f37,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    spl5_23 | ~spl5_3 | ~spl5_6 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f117,f65,f60,f45,f161])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl5_23 <=> r1_tarski(k5_relat_1(sK0,sK0),k5_relat_1(sK1,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl5_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl5_6 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl5_7 <=> v1_relat_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK0,sK0),k5_relat_1(sK1,sK0)) | (~spl5_3 | ~spl5_6 | ~spl5_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f67,f67,f62,f47,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    v1_relat_1(sK1) | ~spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    v1_relat_1(sK0) | ~spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f65])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    spl5_22 | ~spl5_3 | ~spl5_6 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f118,f65,f60,f45,f156])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl5_22 <=> r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK1,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK1,sK1)) | (~spl5_3 | ~spl5_6 | ~spl5_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f67,f62,f47,f30])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    spl5_21 | ~spl5_3 | ~spl5_5 | ~spl5_6 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f119,f65,f60,f55,f45,f151])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl5_5 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) | (~spl5_3 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f57,f67,f62,f47,f30])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f55])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    spl5_20 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f120,f65,f60,f50,f45,f146])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl5_4 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK0,sK3),k5_relat_1(sK1,sK3)) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f52,f67,f62,f47,f30])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f50])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl5_19 | ~spl5_3 | ~spl5_6 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f121,f65,f60,f45,f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl5_19 <=> r1_tarski(k5_relat_1(sK0,sK0),k5_relat_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK0,sK0),k5_relat_1(sK0,sK1)) | (~spl5_3 | ~spl5_6 | ~spl5_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f67,f67,f62,f47,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl5_18 | ~spl5_3 | ~spl5_6 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f122,f65,f60,f45,f136])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl5_18 <=> r1_tarski(k5_relat_1(sK1,sK0),k5_relat_1(sK1,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK1,sK0),k5_relat_1(sK1,sK1)) | (~spl5_3 | ~spl5_6 | ~spl5_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f67,f62,f47,f29])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl5_17 | ~spl5_3 | ~spl5_5 | ~spl5_6 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f123,f65,f60,f55,f45,f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl5_17 <=> r1_tarski(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK2,sK0),k5_relat_1(sK2,sK1)) | (~spl5_3 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f57,f67,f62,f47,f29])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl5_16 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f124,f65,f60,f50,f45,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl5_16 <=> r1_tarski(k5_relat_1(sK3,sK0),k5_relat_1(sK3,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK3,sK0),k5_relat_1(sK3,sK1)) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f52,f67,f62,f47,f29])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl5_15 | ~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f69,f65,f55,f50,f40,f113])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl5_15 <=> r1_tarski(k5_relat_1(sK2,sK0),k5_relat_1(sK3,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl5_2 <=> r1_tarski(sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK2,sK0),k5_relat_1(sK3,sK0)) | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f67,f57,f52,f42,f30])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    r1_tarski(sK2,sK3) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f40])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl5_14 | ~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f70,f60,f55,f50,f40,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl5_14 <=> r1_tarski(k5_relat_1(sK2,sK1),k5_relat_1(sK3,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK2,sK1),k5_relat_1(sK3,sK1)) | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f57,f52,f42,f30])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl5_13 | ~spl5_2 | ~spl5_4 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f71,f55,f50,f40,f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl5_13 <=> r1_tarski(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f57,f57,f52,f42,f30])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl5_12 | ~spl5_2 | ~spl5_4 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f72,f55,f50,f40,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl5_12 <=> r1_tarski(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f52,f57,f52,f42,f30])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl5_11 | ~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f73,f65,f55,f50,f40,f93])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK0,sK3)) | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f67,f57,f52,f42,f29])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl5_10 | ~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f74,f60,f55,f50,f40,f88])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3)) | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f57,f52,f42,f29])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl5_9 | ~spl5_2 | ~spl5_4 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f75,f55,f50,f40,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl5_9 <=> r1_tarski(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f57,f57,f52,f42,f29])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl5_8 | ~spl5_2 | ~spl5_4 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f76,f55,f50,f40,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl5_8 <=> r1_tarski(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f52,f57,f52,f42,f29])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f65])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    (((~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1) & v1_relat_1(sK3)) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3)) & r1_tarski(sK2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X3] : (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3)) & r1_tarski(sK2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) => (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1) & v1_relat_1(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1))) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f60])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f55])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f50])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    v1_relat_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f45])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f40])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    r1_tarski(sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f35])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31255)------------------------------
% 0.21/0.48  % (31255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31255)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31255)Memory used [KB]: 5500
% 0.21/0.48  % (31255)Time elapsed: 0.072 s
% 0.21/0.48  % (31255)------------------------------
% 0.21/0.48  % (31255)------------------------------
% 0.21/0.48  % (31241)Success in time 0.129 s
%------------------------------------------------------------------------------
