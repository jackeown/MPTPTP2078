%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  255 ( 921 expanded)
%              Number of leaves         :   72 ( 407 expanded)
%              Depth                    :    8
%              Number of atoms          :  628 (2309 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f446,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f57,f58,f66,f71,f72,f82,f87,f92,f93,f98,f105,f106,f118,f123,f124,f136,f141,f146,f151,f152,f157,f162,f176,f181,f186,f191,f196,f201,f206,f211,f212,f228,f233,f238,f243,f248,f253,f258,f263,f268,f269,f274,f281,f299,f304,f309,f314,f319,f324,f329,f334,f339,f344,f349,f350,f355,f375,f380,f385,f390,f395,f400,f405,f410,f415,f420,f425,f426,f431,f436,f441,f445])).

fof(f445,plain,
    ( ~ spl4_39
    | ~ spl4_11
    | spl4_13 ),
    inference(avatar_split_clause,[],[f443,f115,f95,f278])).

fof(f278,plain,
    ( spl4_39
  <=> r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f95,plain,
    ( spl4_11
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f115,plain,
    ( spl4_13
  <=> r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f443,plain,
    ( ~ r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl4_11
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f97,f117,f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f117,plain,
    ( ~ r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f97,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f441,plain,
    ( spl4_65
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f356,f95,f68,f438])).

fof(f438,plain,
    ( spl4_65
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f68,plain,
    ( spl4_7
  <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f356,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f70,f97,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f70,plain,
    ( r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f436,plain,
    ( spl4_64
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f357,f95,f89,f433])).

fof(f433,plain,
    ( spl4_64
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f89,plain,
    ( spl4_10
  <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f357,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f91,f97,f30])).

fof(f91,plain,
    ( r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK1,sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f431,plain,
    ( spl4_63
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f358,f95,f84,f428])).

fof(f428,plain,
    ( spl4_63
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f84,plain,
    ( spl4_9
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f358,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f86,f97,f30])).

fof(f86,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK0,sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f426,plain,
    ( spl4_56
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f359,f95,f392])).

fof(f392,plain,
    ( spl4_56
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f359,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f97,f97,f30])).

fof(f425,plain,
    ( spl4_62
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f360,f95,f42,f422])).

fof(f422,plain,
    ( spl4_62
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f42,plain,
    ( spl4_3
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f360,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK0))
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f44,f97,f30])).

fof(f44,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f420,plain,
    ( spl4_61
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f361,f95,f37,f417])).

fof(f417,plain,
    ( spl4_61
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f37,plain,
    ( spl4_2
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f361,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK1))
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f39,f97,f30])).

fof(f39,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f415,plain,
    ( spl4_60
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f362,f95,f54,f412])).

fof(f412,plain,
    ( spl4_60
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f54,plain,
    ( spl4_5
  <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f362,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f56,f97,f30])).

fof(f56,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f410,plain,
    ( spl4_59
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f363,f95,f68,f407])).

fof(f407,plain,
    ( spl4_59
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f363,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f70,f97,f30])).

fof(f405,plain,
    ( spl4_58
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f364,f95,f89,f402])).

fof(f402,plain,
    ( spl4_58
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f364,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f91,f97,f30])).

fof(f400,plain,
    ( spl4_57
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f365,f95,f84,f397])).

fof(f397,plain,
    ( spl4_57
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f365,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f86,f97,f30])).

fof(f395,plain,
    ( spl4_56
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f366,f95,f392])).

fof(f366,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f97,f97,f30])).

fof(f390,plain,
    ( spl4_55
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f367,f95,f42,f387])).

fof(f387,plain,
    ( spl4_55
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f367,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f44,f97,f30])).

fof(f385,plain,
    ( spl4_54
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f368,f95,f37,f382])).

fof(f382,plain,
    ( spl4_54
  <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f368,plain,
    ( r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f39,f97,f30])).

fof(f380,plain,
    ( spl4_53
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f369,f95,f54,f377])).

fof(f377,plain,
    ( spl4_53
  <=> r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f369,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f56,f97,f30])).

fof(f375,plain,
    ( spl4_52
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f370,f95,f372])).

fof(f372,plain,
    ( spl4_52
  <=> m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f370,plain,
    ( m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f97,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f355,plain,
    ( spl4_51
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f282,f89,f68,f352])).

fof(f352,plain,
    ( spl4_51
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f282,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f70,f91,f30])).

fof(f350,plain,
    ( spl4_45
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f283,f89,f321])).

fof(f321,plain,
    ( spl4_45
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f283,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f91,f91,f30])).

fof(f349,plain,
    ( spl4_50
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f284,f89,f84,f346])).

fof(f346,plain,
    ( spl4_50
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f284,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f86,f91,f30])).

fof(f344,plain,
    ( spl4_49
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f285,f89,f42,f341])).

fof(f341,plain,
    ( spl4_49
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f285,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),sK0))
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f44,f91,f30])).

fof(f339,plain,
    ( spl4_48
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f286,f89,f37,f336])).

fof(f336,plain,
    ( spl4_48
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f286,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),sK1))
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f39,f91,f30])).

fof(f334,plain,
    ( spl4_47
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f287,f89,f54,f331])).

fof(f331,plain,
    ( spl4_47
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f287,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f56,f91,f30])).

fof(f329,plain,
    ( spl4_46
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f288,f89,f68,f326])).

fof(f326,plain,
    ( spl4_46
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f288,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f70,f91,f30])).

fof(f324,plain,
    ( spl4_45
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f289,f89,f321])).

fof(f289,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f91,f91,f30])).

fof(f319,plain,
    ( spl4_44
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f290,f89,f84,f316])).

fof(f316,plain,
    ( spl4_44
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f290,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f86,f91,f30])).

fof(f314,plain,
    ( spl4_43
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f291,f89,f42,f311])).

fof(f311,plain,
    ( spl4_43
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f291,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f44,f91,f30])).

fof(f309,plain,
    ( spl4_42
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f292,f89,f37,f306])).

fof(f306,plain,
    ( spl4_42
  <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f292,plain,
    ( r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f39,f91,f30])).

fof(f304,plain,
    ( spl4_41
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f293,f89,f54,f301])).

fof(f301,plain,
    ( spl4_41
  <=> r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f293,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f56,f91,f30])).

fof(f299,plain,
    ( spl4_40
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f294,f89,f296])).

fof(f296,plain,
    ( spl4_40
  <=> m1_subset_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f294,plain,
    ( m1_subset_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f91,f29])).

fof(f281,plain,
    ( spl4_39
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f275,f120,f54,f278])).

fof(f120,plain,
    ( spl4_14
  <=> r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f275,plain,
    ( r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f56,f122,f25])).

fof(f122,plain,
    ( r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f274,plain,
    ( spl4_38
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f213,f84,f68,f271])).

fof(f271,plain,
    ( spl4_38
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f213,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f70,f86,f30])).

fof(f269,plain,
    ( spl4_33
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f214,f84,f245])).

fof(f245,plain,
    ( spl4_33
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f214,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f86,f86,f30])).

fof(f268,plain,
    ( spl4_37
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f215,f84,f42,f265])).

fof(f265,plain,
    ( spl4_37
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f215,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f44,f86,f30])).

fof(f263,plain,
    ( spl4_36
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f216,f84,f37,f260])).

fof(f260,plain,
    ( spl4_36
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f216,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK1))
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f39,f86,f30])).

fof(f258,plain,
    ( spl4_35
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f217,f84,f54,f255])).

fof(f255,plain,
    ( spl4_35
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f217,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f56,f86,f30])).

fof(f253,plain,
    ( spl4_34
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f218,f84,f68,f250])).

fof(f250,plain,
    ( spl4_34
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f218,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f70,f86,f30])).

fof(f248,plain,
    ( spl4_33
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f219,f84,f245])).

fof(f219,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f86,f86,f30])).

fof(f243,plain,
    ( spl4_32
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f220,f84,f42,f240])).

fof(f240,plain,
    ( spl4_32
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f220,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f44,f86,f30])).

fof(f238,plain,
    ( spl4_31
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f221,f84,f37,f235])).

fof(f235,plain,
    ( spl4_31
  <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f221,plain,
    ( r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f39,f86,f30])).

fof(f233,plain,
    ( spl4_30
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f222,f84,f54,f230])).

fof(f230,plain,
    ( spl4_30
  <=> r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

% (801)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
fof(f222,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f56,f86,f30])).

fof(f228,plain,
    ( spl4_29
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f223,f84,f225])).

fof(f225,plain,
    ( spl4_29
  <=> m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f223,plain,
    ( m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f86,f29])).

fof(f212,plain,
    ( spl4_25
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f163,f68,f193])).

fof(f193,plain,
    ( spl4_25
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f163,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f70,f70,f30])).

fof(f211,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f164,f68,f42,f208])).

fof(f208,plain,
    ( spl4_28
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f164,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK0))
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f44,f70,f30])).

fof(f206,plain,
    ( spl4_27
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f165,f68,f37,f203])).

fof(f203,plain,
    ( spl4_27
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f165,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f39,f70,f30])).

fof(f201,plain,
    ( spl4_26
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f166,f68,f54,f198])).

fof(f198,plain,
    ( spl4_26
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f166,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f56,f70,f30])).

fof(f196,plain,
    ( spl4_25
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f167,f68,f193])).

fof(f167,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f70,f70,f30])).

fof(f191,plain,
    ( spl4_24
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f168,f68,f42,f188])).

fof(f188,plain,
    ( spl4_24
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f168,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f44,f70,f30])).

fof(f186,plain,
    ( spl4_23
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f169,f68,f37,f183])).

fof(f183,plain,
    ( spl4_23
  <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f169,plain,
    ( r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f39,f70,f30])).

fof(f181,plain,
    ( spl4_22
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f170,f68,f54,f178])).

fof(f178,plain,
    ( spl4_22
  <=> r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f170,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f56,f70,f30])).

fof(f176,plain,
    ( spl4_21
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f171,f68,f173])).

fof(f173,plain,
    ( spl4_21
  <=> m1_subset_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f171,plain,
    ( m1_subset_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f70,f29])).

fof(f162,plain,
    ( spl4_20
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f125,f54,f37,f159])).

fof(f159,plain,
    ( spl4_20
  <=> r1_tarski(k2_zfmisc_1(sK2,k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f125,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f39,f56,f30])).

fof(f157,plain,
    ( spl4_19
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f126,f54,f42,f154])).

fof(f154,plain,
    ( spl4_19
  <=> r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f126,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK0))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f44,f56,f30])).

fof(f152,plain,
    ( spl4_16
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f127,f54,f138])).

fof(f138,plain,
    ( spl4_16
  <=> r1_tarski(k2_zfmisc_1(sK2,sK2),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f127,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK2),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f56,f56,f30])).

fof(f151,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f128,f54,f37,f148])).

fof(f148,plain,
    ( spl4_18
  <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),sK2),k2_zfmisc_1(sK1,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f128,plain,
    ( r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),sK2),k2_zfmisc_1(sK1,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f39,f56,f30])).

fof(f146,plain,
    ( spl4_17
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f129,f54,f42,f143])).

fof(f143,plain,
    ( spl4_17
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK2),k2_zfmisc_1(sK0,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f129,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK2),k2_zfmisc_1(sK0,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f44,f56,f30])).

fof(f141,plain,
    ( spl4_16
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f130,f54,f138])).

fof(f130,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK2),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f56,f56,f30])).

fof(f136,plain,
    ( spl4_15
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f131,f54,f133])).

fof(f133,plain,
    ( spl4_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f131,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f56,f29])).

fof(f124,plain,
    ( spl4_14
    | spl4_12 ),
    inference(avatar_split_clause,[],[f113,f102,f120])).

fof(f102,plain,
    ( spl4_12
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f113,plain,
    ( r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),sK2)
    | spl4_12 ),
    inference(resolution,[],[f104,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f104,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f102])).

fof(f123,plain,
    ( spl4_14
    | spl4_12 ),
    inference(avatar_split_clause,[],[f110,f102,f120])).

fof(f110,plain,
    ( r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),sK2)
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f104,f26])).

fof(f118,plain,
    ( ~ spl4_13
    | spl4_12 ),
    inference(avatar_split_clause,[],[f111,f102,f115])).

fof(f111,plain,
    ( ~ r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f104,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f106,plain,
    ( ~ spl4_12
    | spl4_1 ),
    inference(avatar_split_clause,[],[f100,f32,f102])).

fof(f32,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f100,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f34,f29])).

fof(f34,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f105,plain,
    ( ~ spl4_12
    | spl4_1 ),
    inference(avatar_split_clause,[],[f99,f32,f102])).

fof(f99,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f34,f29])).

fof(f98,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f73,f42,f37,f95])).

fof(f73,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f39,f44,f30])).

fof(f93,plain,
    ( spl4_9
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f74,f42,f84])).

fof(f74,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK0,sK0))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f44,f44,f30])).

fof(f92,plain,
    ( spl4_10
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f75,f42,f37,f89])).

fof(f75,plain,
    ( r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK1,sK0))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f39,f44,f30])).

fof(f87,plain,
    ( spl4_9
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f76,f42,f84])).

fof(f76,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK0,sK0))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f44,f44,f30])).

fof(f82,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f77,f42,f79])).

fof(f79,plain,
    ( spl4_8
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f77,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f44,f29])).

fof(f72,plain,
    ( spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f59,f37,f68])).

fof(f59,plain,
    ( r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK1))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f39,f39,f30])).

fof(f71,plain,
    ( spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f60,f37,f68])).

fof(f60,plain,
    ( r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK1))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f39,f39,f30])).

fof(f66,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f37,f63])).

fof(f63,plain,
    ( spl4_6
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f61,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f39,f29])).

fof(f58,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f52,f47,f54])).

fof(f47,plain,
    ( spl4_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f52,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl4_4 ),
    inference(resolution,[],[f49,f24])).

% (805)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f49,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f57,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f51,f47,f54])).

fof(f51,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f49,f24])).

fof(f50,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & r1_tarski(k2_relat_1(sK2),sK1)
    & r1_tarski(k1_relat_1(sK2),sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & r1_tarski(k2_relat_1(X2),X1)
        & r1_tarski(k1_relat_1(X2),X0)
        & v1_relat_1(X2) )
   => ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & r1_tarski(k2_relat_1(sK2),sK1)
      & r1_tarski(k1_relat_1(sK2),sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & r1_tarski(k2_relat_1(X2),X1)
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & r1_tarski(k2_relat_1(X2),X1)
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r1_tarski(k2_relat_1(X2),X1)
            & r1_tarski(k1_relat_1(X2),X0) )
         => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f45,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f23,f32])).

fof(f23,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (799)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.47  % (788)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.49  % (800)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (798)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.50  % (789)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.50  % (792)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.50  % (799)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f446,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f57,f58,f66,f71,f72,f82,f87,f92,f93,f98,f105,f106,f118,f123,f124,f136,f141,f146,f151,f152,f157,f162,f176,f181,f186,f191,f196,f201,f206,f211,f212,f228,f233,f238,f243,f248,f253,f258,f263,f268,f269,f274,f281,f299,f304,f309,f314,f319,f324,f329,f334,f339,f344,f349,f350,f355,f375,f380,f385,f390,f395,f400,f405,f410,f415,f420,f425,f426,f431,f436,f441,f445])).
% 0.21/0.50  fof(f445,plain,(
% 0.21/0.50    ~spl4_39 | ~spl4_11 | spl4_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f443,f115,f95,f278])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    spl4_39 <=> r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl4_11 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl4_13 <=> r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.50  fof(f443,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | (~spl4_11 | spl4_13)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f97,f117,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | spl4_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1)) | ~spl4_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f95])).
% 0.21/0.50  fof(f441,plain,(
% 0.21/0.50    spl4_65 | ~spl4_7 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f356,f95,f68,f438])).
% 0.21/0.50  fof(f438,plain,(
% 0.21/0.50    spl4_65 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK1,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl4_7 <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.50  fof(f356,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK1,sK1))) | (~spl4_7 | ~spl4_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f70,f97,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK1)) | ~spl4_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f68])).
% 0.21/0.50  fof(f436,plain,(
% 0.21/0.50    spl4_64 | ~spl4_10 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f357,f95,f89,f433])).
% 0.21/0.50  fof(f433,plain,(
% 0.21/0.50    spl4_64 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl4_10 <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK1,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.50  fof(f357,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK1,sK0))) | (~spl4_10 | ~spl4_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f91,f97,f30])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK1,sK0)) | ~spl4_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f89])).
% 0.21/0.50  fof(f431,plain,(
% 0.21/0.50    spl4_63 | ~spl4_9 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f358,f95,f84,f428])).
% 0.21/0.50  fof(f428,plain,(
% 0.21/0.50    spl4_63 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl4_9 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK0))) | (~spl4_9 | ~spl4_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f86,f97,f30])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK0,sK0)) | ~spl4_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f84])).
% 0.21/0.50  fof(f426,plain,(
% 0.21/0.50    spl4_56 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f359,f95,f392])).
% 0.21/0.50  fof(f392,plain,(
% 0.21/0.50    spl4_56 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))) | ~spl4_11),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f97,f97,f30])).
% 0.21/0.50  fof(f425,plain,(
% 0.21/0.50    spl4_62 | ~spl4_3 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f360,f95,f42,f422])).
% 0.21/0.50  fof(f422,plain,(
% 0.21/0.50    spl4_62 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    spl4_3 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK0)) | (~spl4_3 | ~spl4_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f97,f30])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    r1_tarski(k1_relat_1(sK2),sK0) | ~spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f42])).
% 0.21/0.50  fof(f420,plain,(
% 0.21/0.50    spl4_61 | ~spl4_2 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f361,f95,f37,f417])).
% 0.21/0.50  fof(f417,plain,(
% 0.21/0.50    spl4_61 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    spl4_2 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK1)) | (~spl4_2 | ~spl4_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f97,f30])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),sK1) | ~spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f37])).
% 0.21/0.50  fof(f415,plain,(
% 0.21/0.50    spl4_60 | ~spl4_5 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f362,f95,f54,f412])).
% 0.21/0.50  fof(f412,plain,(
% 0.21/0.50    spl4_60 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl4_5 <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.50  fof(f362,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl4_5 | ~spl4_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f97,f30])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | ~spl4_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f54])).
% 0.21/0.50  fof(f410,plain,(
% 0.21/0.50    spl4_59 | ~spl4_7 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f363,f95,f68,f407])).
% 0.21/0.50  fof(f407,plain,(
% 0.21/0.50    spl4_59 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 0.21/0.50  fof(f363,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK0,sK1))) | (~spl4_7 | ~spl4_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f70,f97,f30])).
% 0.21/0.50  fof(f405,plain,(
% 0.21/0.50    spl4_58 | ~spl4_10 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f364,f95,f89,f402])).
% 0.21/0.50  fof(f402,plain,(
% 0.21/0.50    spl4_58 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 0.21/0.50  fof(f364,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK0,sK1))) | (~spl4_10 | ~spl4_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f91,f97,f30])).
% 0.21/0.50  fof(f400,plain,(
% 0.21/0.50    spl4_57 | ~spl4_9 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f365,f95,f84,f397])).
% 0.21/0.50  fof(f397,plain,(
% 0.21/0.50    spl4_57 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.21/0.50  fof(f365,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK0,sK1))) | (~spl4_9 | ~spl4_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f86,f97,f30])).
% 0.21/0.50  fof(f395,plain,(
% 0.21/0.50    spl4_56 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f366,f95,f392])).
% 0.21/0.50  fof(f366,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))) | ~spl4_11),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f97,f97,f30])).
% 0.21/0.50  fof(f390,plain,(
% 0.21/0.50    spl4_55 | ~spl4_3 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f367,f95,f42,f387])).
% 0.21/0.50  fof(f387,plain,(
% 0.21/0.50    spl4_55 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.21/0.50  fof(f367,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK1))) | (~spl4_3 | ~spl4_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f97,f30])).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    spl4_54 | ~spl4_2 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f368,f95,f37,f382])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    spl4_54 <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK0,sK1))) | (~spl4_2 | ~spl4_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f97,f30])).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    spl4_53 | ~spl4_5 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f369,f95,f54,f377])).
% 0.21/0.50  fof(f377,plain,(
% 0.21/0.50    spl4_53 <=> r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.21/0.50  fof(f369,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1))) | (~spl4_5 | ~spl4_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f97,f30])).
% 0.21/0.50  fof(f375,plain,(
% 0.21/0.50    spl4_52 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f370,f95,f372])).
% 0.21/0.50  fof(f372,plain,(
% 0.21/0.50    spl4_52 <=> m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_11),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f97,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f355,plain,(
% 0.21/0.50    spl4_51 | ~spl4_7 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f282,f89,f68,f352])).
% 0.21/0.50  fof(f352,plain,(
% 0.21/0.50    spl4_51 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK1,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK1,sK1))) | (~spl4_7 | ~spl4_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f70,f91,f30])).
% 0.21/0.50  fof(f350,plain,(
% 0.21/0.50    spl4_45 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f283,f89,f321])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    spl4_45 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK1,sK0))) | ~spl4_10),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f91,f91,f30])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    spl4_50 | ~spl4_9 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f284,f89,f84,f346])).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    spl4_50 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK0,sK0))) | (~spl4_9 | ~spl4_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f86,f91,f30])).
% 0.21/0.50  fof(f344,plain,(
% 0.21/0.50    spl4_49 | ~spl4_3 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f285,f89,f42,f341])).
% 0.21/0.50  fof(f341,plain,(
% 0.21/0.50    spl4_49 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),sK0)) | (~spl4_3 | ~spl4_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f91,f30])).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    spl4_48 | ~spl4_2 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f286,f89,f37,f336])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    spl4_48 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),sK1)) | (~spl4_2 | ~spl4_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f91,f30])).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    spl4_47 | ~spl4_5 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f287,f89,f54,f331])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    spl4_47 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl4_5 | ~spl4_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f91,f30])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    spl4_46 | ~spl4_7 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f288,f89,f68,f326])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    spl4_46 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK1,sK0))) | (~spl4_7 | ~spl4_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f70,f91,f30])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    spl4_45 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f289,f89,f321])).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK1,sK0))) | ~spl4_10),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f91,f91,f30])).
% 0.21/0.50  fof(f319,plain,(
% 0.21/0.50    spl4_44 | ~spl4_9 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f290,f89,f84,f316])).
% 0.21/0.50  fof(f316,plain,(
% 0.21/0.50    spl4_44 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK1,sK0))) | (~spl4_9 | ~spl4_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f86,f91,f30])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    spl4_43 | ~spl4_3 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f291,f89,f42,f311])).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    spl4_43 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK0))) | (~spl4_3 | ~spl4_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f91,f30])).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    spl4_42 | ~spl4_2 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f292,f89,f37,f306])).
% 0.21/0.50  fof(f306,plain,(
% 0.21/0.50    spl4_42 <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK1,sK0))) | (~spl4_2 | ~spl4_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f91,f30])).
% 0.21/0.50  fof(f304,plain,(
% 0.21/0.50    spl4_41 | ~spl4_5 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f293,f89,f54,f301])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    spl4_41 <=> r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK0))) | (~spl4_5 | ~spl4_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f91,f30])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    spl4_40 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f294,f89,f296])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    spl4_40 <=> m1_subset_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    m1_subset_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_10),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f91,f29])).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    spl4_39 | ~spl4_5 | ~spl4_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f275,f120,f54,f278])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl4_14 <=> r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | (~spl4_5 | ~spl4_14)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f122,f25])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),sK2) | ~spl4_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    spl4_38 | ~spl4_7 | ~spl4_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f213,f84,f68,f271])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    spl4_38 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK1,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK1,sK1))) | (~spl4_7 | ~spl4_9)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f70,f86,f30])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    spl4_33 | ~spl4_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f214,f84,f245])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    spl4_33 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK0,sK0))) | ~spl4_9),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f86,f86,f30])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    spl4_37 | ~spl4_3 | ~spl4_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f215,f84,f42,f265])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    spl4_37 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) | (~spl4_3 | ~spl4_9)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f86,f30])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    spl4_36 | ~spl4_2 | ~spl4_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f216,f84,f37,f260])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    spl4_36 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK1)) | (~spl4_2 | ~spl4_9)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f86,f30])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    spl4_35 | ~spl4_5 | ~spl4_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f217,f84,f54,f255])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    spl4_35 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl4_5 | ~spl4_9)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f86,f30])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    spl4_34 | ~spl4_7 | ~spl4_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f218,f84,f68,f250])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    spl4_34 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK0,sK0))) | (~spl4_7 | ~spl4_9)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f70,f86,f30])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    spl4_33 | ~spl4_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f219,f84,f245])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),k2_zfmisc_1(sK0,sK0))) | ~spl4_9),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f86,f86,f30])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    spl4_32 | ~spl4_3 | ~spl4_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f220,f84,f42,f240])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    spl4_32 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK0))) | (~spl4_3 | ~spl4_9)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f86,f30])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    spl4_31 | ~spl4_2 | ~spl4_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f221,f84,f37,f235])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    spl4_31 <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK0,sK0))) | (~spl4_2 | ~spl4_9)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f86,f30])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    spl4_30 | ~spl4_5 | ~spl4_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f222,f84,f54,f230])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    spl4_30 <=> r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.50  % (801)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK0))) | (~spl4_5 | ~spl4_9)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f86,f30])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    spl4_29 | ~spl4_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f223,f84,f225])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    spl4_29 <=> m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_9),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f86,f29])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    spl4_25 | ~spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f163,f68,f193])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    spl4_25 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK1,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK1,sK1))) | ~spl4_7),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f70,f70,f30])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    spl4_28 | ~spl4_3 | ~spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f164,f68,f42,f208])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    spl4_28 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK0)) | (~spl4_3 | ~spl4_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f70,f30])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    spl4_27 | ~spl4_2 | ~spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f165,f68,f37,f203])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    spl4_27 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)) | (~spl4_2 | ~spl4_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f70,f30])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    spl4_26 | ~spl4_5 | ~spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f166,f68,f54,f198])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    spl4_26 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),sK2),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl4_5 | ~spl4_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f70,f30])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    spl4_25 | ~spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f167,f68,f193])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK1,sK1))) | ~spl4_7),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f70,f70,f30])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    spl4_24 | ~spl4_3 | ~spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f168,f68,f42,f188])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    spl4_24 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK1))) | (~spl4_3 | ~spl4_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f70,f30])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    spl4_23 | ~spl4_2 | ~spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f169,f68,f37,f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    spl4_23 <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK1,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(sK1,k2_zfmisc_1(sK1,sK1))) | (~spl4_2 | ~spl4_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f70,f30])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    spl4_22 | ~spl4_5 | ~spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f170,f68,f54,f178])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl4_22 <=> r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(sK2,k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2))),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK1))) | (~spl4_5 | ~spl4_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f70,f30])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    spl4_21 | ~spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f171,f68,f173])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    spl4_21 <=> m1_subset_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    m1_subset_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~spl4_7),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f70,f29])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl4_20 | ~spl4_2 | ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f125,f54,f37,f159])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl4_20 <=> r1_tarski(k2_zfmisc_1(sK2,k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(sK2,k2_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK1)) | (~spl4_2 | ~spl4_5)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f56,f30])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl4_19 | ~spl4_3 | ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f126,f54,f42,f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    spl4_19 <=> r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK2)),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK0)) | (~spl4_3 | ~spl4_5)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f56,f30])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl4_16 | ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f127,f54,f138])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl4_16 <=> r1_tarski(k2_zfmisc_1(sK2,sK2),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(sK2,sK2),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl4_5),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f56,f30])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    spl4_18 | ~spl4_2 | ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f128,f54,f37,f148])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    spl4_18 <=> r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),sK2),k2_zfmisc_1(sK1,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),sK2),k2_zfmisc_1(sK1,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl4_2 | ~spl4_5)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f56,f30])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    spl4_17 | ~spl4_3 | ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f129,f54,f42,f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl4_17 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK2),k2_zfmisc_1(sK0,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK2),k2_zfmisc_1(sK0,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl4_3 | ~spl4_5)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f56,f30])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    spl4_16 | ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f130,f54,f138])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(sK2,sK2),k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl4_5),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f56,f30])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl4_15 | ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f131,f54,f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    spl4_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl4_5),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f29])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl4_14 | spl4_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f113,f102,f120])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl4_12 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),sK2) | spl4_12),
% 0.21/0.50    inference(resolution,[],[f104,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ~r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | spl4_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl4_14 | spl4_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f110,f102,f120])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),sK2) | spl4_12),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f104,f26])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ~spl4_13 | spl4_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f111,f102,f115])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK2,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | spl4_12),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f104,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ~spl4_12 | spl4_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f100,f32,f102])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ~r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 0.21/0.50    inference(resolution,[],[f34,f29])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f32])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ~spl4_12 | spl4_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f99,f32,f102])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ~r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f34,f29])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl4_11 | ~spl4_2 | ~spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f73,f42,f37,f95])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK0,sK1)) | (~spl4_2 | ~spl4_3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f44,f30])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl4_9 | ~spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f74,f42,f84])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK0,sK0)) | ~spl4_3),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f44,f30])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl4_10 | ~spl4_2 | ~spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f75,f42,f37,f89])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK1,sK0)) | (~spl4_2 | ~spl4_3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f44,f30])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl4_9 | ~spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f76,f42,f84])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)),k2_zfmisc_1(sK0,sK0)) | ~spl4_3),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f44,f30])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl4_8 | ~spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f77,f42,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl4_8 <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f29])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl4_7 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f37,f68])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK1)) | ~spl4_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f39,f30])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    spl4_7 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f60,f37,f68])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    r1_tarski(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(sK2)),k2_zfmisc_1(sK1,sK1)) | ~spl4_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f39,f30])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl4_6 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f61,f37,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl4_6 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl4_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f39,f29])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    spl4_5 | ~spl4_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f47,f54])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    spl4_4 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | ~spl4_4),
% 0.21/0.50    inference(resolution,[],[f49,f24])).
% 0.21/0.50  % (805)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl4_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f47])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl4_5 | ~spl4_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f47,f54])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | ~spl4_4),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f49,f24])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl4_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f20,f47])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & r1_tarski(k2_relat_1(sK2),sK1) & r1_tarski(k1_relat_1(sK2),sK0) & v1_relat_1(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2)) => (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & r1_tarski(k2_relat_1(sK2),sK1) & r1_tarski(k1_relat_1(sK2),sK0) & v1_relat_1(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & (r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0))) & v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f42])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f37])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ~spl4_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f32])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (799)------------------------------
% 0.21/0.50  % (799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (799)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (799)Memory used [KB]: 5500
% 0.21/0.50  % (799)Time elapsed: 0.082 s
% 0.21/0.50  % (799)------------------------------
% 0.21/0.50  % (799)------------------------------
% 0.21/0.50  % (790)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.50  % (783)Success in time 0.147 s
%------------------------------------------------------------------------------
