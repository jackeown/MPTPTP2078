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
% DateTime   : Thu Dec  3 13:15:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 422 expanded)
%              Number of leaves         :   48 ( 205 expanded)
%              Depth                    :   10
%              Number of atoms          :  829 (2809 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f482,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f104,f124,f129,f134,f139,f144,f149,f154,f159,f164,f169,f175,f181,f188,f212,f218,f237,f258,f274,f283,f301,f302,f325,f349,f416,f451,f458,f481])).

fof(f481,plain,
    ( spl14_53
    | ~ spl14_22
    | ~ spl14_32 ),
    inference(avatar_split_clause,[],[f460,f279,f210,f455])).

fof(f455,plain,
    ( spl14_53
  <=> sP1(sK2,k1_tops_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_53])])).

fof(f210,plain,
    ( spl14_22
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).

fof(f279,plain,
    ( spl14_32
  <=> m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).

fof(f460,plain,
    ( sP1(sK2,k1_tops_1(sK2,sK4))
    | ~ spl14_22
    | ~ spl14_32 ),
    inference(unit_resulting_resolution,[],[f280,f211])).

fof(f211,plain,
    ( ! [X0] :
        ( sP1(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl14_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f280,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl14_32 ),
    inference(avatar_component_clause,[],[f279])).

fof(f458,plain,
    ( ~ spl14_53
    | ~ spl14_26
    | spl14_52 ),
    inference(avatar_split_clause,[],[f453,f448,f234,f455])).

fof(f234,plain,
    ( spl14_26
  <=> v3_pre_topc(k1_tops_1(sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).

fof(f448,plain,
    ( spl14_52
  <=> sP0(k1_tops_1(sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_52])])).

fof(f453,plain,
    ( ~ sP1(sK2,k1_tops_1(sK2,sK4))
    | ~ spl14_26
    | spl14_52 ),
    inference(unit_resulting_resolution,[],[f236,f450,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v3_pre_topc(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v3_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v3_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f450,plain,
    ( ~ sP0(k1_tops_1(sK2,sK4),sK2)
    | spl14_52 ),
    inference(avatar_component_clause,[],[f448])).

fof(f236,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK4),sK2)
    | ~ spl14_26 ),
    inference(avatar_component_clause,[],[f234])).

fof(f451,plain,
    ( ~ spl14_52
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_39
    | ~ spl14_48 ),
    inference(avatar_split_clause,[],[f446,f413,f346,f141,f136,f448])).

fof(f136,plain,
    ( spl14_11
  <=> v3_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f141,plain,
    ( spl14_12
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f346,plain,
    ( spl14_39
  <=> r1_tarski(sK5,k1_tops_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_39])])).

fof(f413,plain,
    ( spl14_48
  <=> sP9(k1_tops_1(sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_48])])).

fof(f446,plain,
    ( ~ sP0(k1_tops_1(sK2,sK4),sK2)
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_39
    | ~ spl14_48 ),
    inference(unit_resulting_resolution,[],[f138,f143,f348,f415,f84])).

fof(f84,plain,(
    ! [X6,X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X6,X0)
      | ~ sP9(X0,X6) ) ),
    inference(general_splitting,[],[f65,f83_D])).

fof(f83,plain,(
    ! [X6,X0,X5] :
      ( sP9(X0,X6)
      | ~ r2_hidden(X5,X6)
      | r2_hidden(X5,X0) ) ),
    inference(cnf_transformation,[],[f83_D])).

fof(f83_D,plain,(
    ! [X6,X0] :
      ( ! [X5] :
          ( ~ r2_hidden(X5,X6)
          | r2_hidden(X5,X0) )
    <=> ~ sP9(X0,X6) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f65,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X0)
      | ~ r2_hidden(X5,X6)
      | ~ r1_tarski(X6,X0)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( ~ r2_hidden(sK6(X0,X1),X3)
                | ~ r1_tarski(X3,X0)
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK6(X0,X1),X0) )
          & ( ( r2_hidden(sK6(X0,X1),sK7(X0,X1))
              & r1_tarski(sK7(X0,X1),X0)
              & v3_pre_topc(sK7(X0,X1),X1)
              & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK6(X0,X1),X0) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X0)
              | ! [X6] :
                  ( ~ r2_hidden(X5,X6)
                  | ~ r1_tarski(X6,X0)
                  | ~ v3_pre_topc(X6,X1)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
            & ( ( r2_hidden(X5,sK8(X0,X1,X5))
                & r1_tarski(sK8(X0,X1,X5),X0)
                & v3_pre_topc(sK8(X0,X1,X5),X1)
                & m1_subset_1(sK8(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X5,X0) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f42,f45,f44,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X2,X3)
                | ~ r1_tarski(X3,X0)
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X2,X0) )
          & ( ? [X4] :
                ( r2_hidden(X2,X4)
                & r1_tarski(X4,X0)
                & v3_pre_topc(X4,X1)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X2,X0) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(sK6(X0,X1),X3)
              | ~ r1_tarski(X3,X0)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( ? [X4] :
              ( r2_hidden(sK6(X0,X1),X4)
              & r1_tarski(X4,X0)
              & v3_pre_topc(X4,X1)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(sK6(X0,X1),X4)
          & r1_tarski(X4,X0)
          & v3_pre_topc(X4,X1)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(sK6(X0,X1),sK7(X0,X1))
        & r1_tarski(sK7(X0,X1),X0)
        & v3_pre_topc(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( r2_hidden(X5,X7)
          & r1_tarski(X7,X0)
          & v3_pre_topc(X7,X1)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(X5,sK8(X0,X1,X5))
        & r1_tarski(sK8(X0,X1,X5),X0)
        & v3_pre_topc(sK8(X0,X1,X5),X1)
        & m1_subset_1(sK8(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r1_tarski(X3,X0)
                  | ~ v3_pre_topc(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X2,X0) )
            & ( ? [X4] :
                  ( r2_hidden(X2,X4)
                  & r1_tarski(X4,X0)
                  & v3_pre_topc(X4,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X2,X0) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X0)
              | ! [X6] :
                  ( ~ r2_hidden(X5,X6)
                  | ~ r1_tarski(X6,X0)
                  | ~ v3_pre_topc(X6,X1)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
            & ( ? [X7] :
                  ( r2_hidden(X5,X7)
                  & r1_tarski(X7,X0)
                  & v3_pre_topc(X7,X1)
                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X5,X0) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r1_tarski(X3,X1)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X2,X3)
                  & r1_tarski(X3,X1)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r1_tarski(X3,X1)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X3] :
                  ( r2_hidden(X2,X3)
                  & r1_tarski(X3,X1)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X2,X3)
              & r1_tarski(X3,X1)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f415,plain,
    ( sP9(k1_tops_1(sK2,sK4),sK5)
    | ~ spl14_48 ),
    inference(avatar_component_clause,[],[f413])).

fof(f348,plain,
    ( r1_tarski(sK5,k1_tops_1(sK2,sK4))
    | ~ spl14_39 ),
    inference(avatar_component_clause,[],[f346])).

fof(f143,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f138,plain,
    ( v3_pre_topc(sK5,sK2)
    | ~ spl14_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f416,plain,
    ( spl14_48
    | ~ spl14_9
    | spl14_28 ),
    inference(avatar_split_clause,[],[f411,f255,f126,f413])).

fof(f126,plain,
    ( spl14_9
  <=> r2_hidden(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f255,plain,
    ( spl14_28
  <=> r2_hidden(sK3,k1_tops_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).

fof(f411,plain,
    ( sP9(k1_tops_1(sK2,sK4),sK5)
    | ~ spl14_9
    | spl14_28 ),
    inference(unit_resulting_resolution,[],[f128,f256,f83])).

fof(f256,plain,
    ( ~ r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | spl14_28 ),
    inference(avatar_component_clause,[],[f255])).

fof(f128,plain,
    ( r2_hidden(sK3,sK5)
    | ~ spl14_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f349,plain,
    ( spl14_39
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_13
    | ~ spl14_15
    | ~ spl14_37 ),
    inference(avatar_split_clause,[],[f344,f322,f156,f146,f141,f131,f346])).

fof(f131,plain,
    ( spl14_10
  <=> r1_tarski(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f146,plain,
    ( spl14_13
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

fof(f156,plain,
    ( spl14_15
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).

fof(f322,plain,
    ( spl14_37
  <=> sK5 = k1_tops_1(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_37])])).

fof(f344,plain,
    ( r1_tarski(sK5,k1_tops_1(sK2,sK4))
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_13
    | ~ spl14_15
    | ~ spl14_37 ),
    inference(forward_demodulation,[],[f331,f324])).

fof(f324,plain,
    ( sK5 = k1_tops_1(sK2,sK5)
    | ~ spl14_37 ),
    inference(avatar_component_clause,[],[f322])).

fof(f331,plain,
    ( r1_tarski(k1_tops_1(sK2,sK5),k1_tops_1(sK2,sK4))
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_13
    | ~ spl14_15 ),
    inference(unit_resulting_resolution,[],[f158,f133,f148,f143,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f148,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl14_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f133,plain,
    ( r1_tarski(sK5,sK4)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f158,plain,
    ( l1_pre_topc(sK2)
    | ~ spl14_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f325,plain,
    ( spl14_37
    | ~ spl14_12
    | ~ spl14_2
    | ~ spl14_11
    | ~ spl14_15 ),
    inference(avatar_split_clause,[],[f320,f156,f136,f98,f141,f322])).

fof(f98,plain,
    ( spl14_2
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f320,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK5 = k1_tops_1(sK2,sK5)
    | ~ spl14_2
    | ~ spl14_11
    | ~ spl14_15 ),
    inference(resolution,[],[f138,f245])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | k1_tops_1(sK2,X0) = X0 )
    | ~ spl14_2
    | ~ spl14_15 ),
    inference(resolution,[],[f99,f158])).

fof(f99,plain,
    ( ! [X3,X1] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f302,plain,
    ( spl14_7
    | ~ spl14_13
    | ~ spl14_14
    | ~ spl14_15
    | ~ spl14_16
    | spl14_17
    | ~ spl14_28 ),
    inference(avatar_split_clause,[],[f276,f255,f166,f161,f156,f151,f146,f118])).

fof(f118,plain,
    ( spl14_7
  <=> m1_connsp_2(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f151,plain,
    ( spl14_14
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f161,plain,
    ( spl14_16
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).

fof(f166,plain,
    ( spl14_17
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f276,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ spl14_13
    | ~ spl14_14
    | ~ spl14_15
    | ~ spl14_16
    | spl14_17
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f168,f163,f158,f153,f148,f257,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f257,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | ~ spl14_28 ),
    inference(avatar_component_clause,[],[f255])).

fof(f153,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f163,plain,
    ( v2_pre_topc(sK2)
    | ~ spl14_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f168,plain,
    ( ~ v2_struct_0(sK2)
    | spl14_17 ),
    inference(avatar_component_clause,[],[f166])).

fof(f301,plain,
    ( spl14_32
    | ~ spl14_31 ),
    inference(avatar_split_clause,[],[f300,f271,f279])).

fof(f271,plain,
    ( spl14_31
  <=> r1_tarski(k1_tops_1(sK2,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_31])])).

fof(f300,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl14_31 ),
    inference(unit_resulting_resolution,[],[f273,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f273,plain,
    ( r1_tarski(k1_tops_1(sK2,sK4),u1_struct_0(sK2))
    | ~ spl14_31 ),
    inference(avatar_component_clause,[],[f271])).

fof(f283,plain,
    ( ~ spl14_23
    | ~ spl14_26
    | ~ spl14_32
    | ~ spl14_8
    | ~ spl14_28 ),
    inference(avatar_split_clause,[],[f277,f255,f122,f279,f234,f215])).

fof(f215,plain,
    ( spl14_23
  <=> r1_tarski(k1_tops_1(sK2,sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_23])])).

fof(f122,plain,
    ( spl14_8
  <=> ! [X3] :
        ( ~ r2_hidden(sK3,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_pre_topc(X3,sK2)
        | ~ r1_tarski(X3,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f277,plain,
    ( ~ m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(k1_tops_1(sK2,sK4),sK2)
    | ~ r1_tarski(k1_tops_1(sK2,sK4),sK4)
    | ~ spl14_8
    | ~ spl14_28 ),
    inference(resolution,[],[f257,f123])).

fof(f123,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK3,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_pre_topc(X3,sK2)
        | ~ r1_tarski(X3,sK4) )
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f274,plain,
    ( spl14_31
    | ~ spl14_19
    | ~ spl14_23 ),
    inference(avatar_split_clause,[],[f263,f215,f178,f271])).

fof(f178,plain,
    ( spl14_19
  <=> r1_tarski(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f263,plain,
    ( r1_tarski(k1_tops_1(sK2,sK4),u1_struct_0(sK2))
    | ~ spl14_19
    | ~ spl14_23 ),
    inference(unit_resulting_resolution,[],[f180,f217,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f217,plain,
    ( r1_tarski(k1_tops_1(sK2,sK4),sK4)
    | ~ spl14_23 ),
    inference(avatar_component_clause,[],[f215])).

fof(f180,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2))
    | ~ spl14_19 ),
    inference(avatar_component_clause,[],[f178])).

fof(f258,plain,
    ( spl14_28
    | ~ spl14_7
    | ~ spl14_13
    | ~ spl14_14
    | ~ spl14_15
    | ~ spl14_16
    | spl14_17 ),
    inference(avatar_split_clause,[],[f252,f166,f161,f156,f151,f146,f118,f255])).

fof(f252,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | ~ spl14_7
    | ~ spl14_13
    | ~ spl14_14
    | ~ spl14_15
    | ~ spl14_16
    | spl14_17 ),
    inference(unit_resulting_resolution,[],[f168,f163,f158,f119,f153,f148,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f119,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ spl14_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f237,plain,
    ( spl14_26
    | ~ spl14_13
    | ~ spl14_15
    | ~ spl14_16 ),
    inference(avatar_split_clause,[],[f232,f161,f156,f146,f234])).

fof(f232,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK4),sK2)
    | ~ spl14_13
    | ~ spl14_15
    | ~ spl14_16 ),
    inference(unit_resulting_resolution,[],[f163,f158,f148,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f218,plain,
    ( spl14_23
    | ~ spl14_13
    | ~ spl14_15 ),
    inference(avatar_split_clause,[],[f213,f156,f146,f215])).

fof(f213,plain,
    ( r1_tarski(k1_tops_1(sK2,sK4),sK4)
    | ~ spl14_13
    | ~ spl14_15 ),
    inference(unit_resulting_resolution,[],[f158,f148,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f212,plain,
    ( ~ spl14_16
    | spl14_22
    | ~ spl14_15 ),
    inference(avatar_split_clause,[],[f203,f156,f210,f161])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP1(sK2,X0)
        | ~ v2_pre_topc(sK2) )
    | ~ spl14_15 ),
    inference(resolution,[],[f71,f158])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f15,f30,f29])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_1)).

fof(f188,plain,
    ( spl14_18
    | ~ spl14_13 ),
    inference(avatar_split_clause,[],[f183,f146,f172])).

fof(f172,plain,
    ( spl14_18
  <=> sP12(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f183,plain,
    ( sP12(sK2)
    | ~ spl14_13 ),
    inference(unit_resulting_resolution,[],[f148,f89])).

fof(f89,plain,(
    ! [X2,X0] :
      ( sP12(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f89_D])).

fof(f89_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    <=> ~ sP12(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP12])])).

fof(f181,plain,
    ( spl14_19
    | ~ spl14_13 ),
    inference(avatar_split_clause,[],[f176,f146,f178])).

fof(f176,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2))
    | ~ spl14_13 ),
    inference(unit_resulting_resolution,[],[f148,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f175,plain,
    ( ~ spl14_18
    | ~ spl14_3
    | ~ spl14_15
    | ~ spl14_16 ),
    inference(avatar_split_clause,[],[f170,f161,f156,f102,f172])).

fof(f102,plain,
    ( spl14_3
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ sP12(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f170,plain,
    ( ~ sP12(sK2)
    | ~ spl14_3
    | ~ spl14_15
    | ~ spl14_16 ),
    inference(unit_resulting_resolution,[],[f163,f158,f103])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ sP12(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f169,plain,(
    ~ spl14_17 ),
    inference(avatar_split_clause,[],[f49,f166])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK3,X3)
          | ~ r1_tarski(X3,sK4)
          | ~ v3_pre_topc(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      | ~ m1_connsp_2(sK4,sK2,sK3) )
    & ( ( r2_hidden(sK3,sK5)
        & r1_tarski(sK5,sK4)
        & v3_pre_topc(sK5,sK2)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) )
      | m1_connsp_2(sK4,sK2,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f34,f38,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | m1_connsp_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,sK2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
                | ~ m1_connsp_2(X2,sK2,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,sK2)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
                | m1_connsp_2(X2,sK2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              | ~ m1_connsp_2(X2,sK2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,sK2)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
              | m1_connsp_2(X2,sK2,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(sK3,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK2)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            | ~ m1_connsp_2(X2,sK2,sK3) )
          & ( ? [X4] :
                ( r2_hidden(sK3,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK2)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
            | m1_connsp_2(X2,sK2,sK3) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(sK3,X3)
              | ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          | ~ m1_connsp_2(X2,sK2,sK3) )
        & ( ? [X4] :
              ( r2_hidden(sK3,X4)
              & r1_tarski(X4,X2)
              & v3_pre_topc(X4,sK2)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
          | m1_connsp_2(X2,sK2,sK3) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(sK3,X3)
            | ~ r1_tarski(X3,sK4)
            | ~ v3_pre_topc(X3,sK2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        | ~ m1_connsp_2(sK4,sK2,sK3) )
      & ( ? [X4] :
            ( r2_hidden(sK3,X4)
            & r1_tarski(X4,sK4)
            & v3_pre_topc(X4,sK2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
        | m1_connsp_2(sK4,sK2,sK3) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X4] :
        ( r2_hidden(sK3,X4)
        & r1_tarski(X4,sK4)
        & v3_pre_topc(X4,sK2)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( r2_hidden(sK3,sK5)
      & r1_tarski(sK5,sK4)
      & v3_pre_topc(sK5,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m1_connsp_2(X2,X0,X1)
                <=> ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f164,plain,(
    spl14_16 ),
    inference(avatar_split_clause,[],[f50,f161])).

fof(f50,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f159,plain,(
    spl14_15 ),
    inference(avatar_split_clause,[],[f51,f156])).

fof(f51,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f154,plain,(
    spl14_14 ),
    inference(avatar_split_clause,[],[f52,f151])).

fof(f52,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f149,plain,(
    spl14_13 ),
    inference(avatar_split_clause,[],[f53,f146])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f144,plain,
    ( spl14_7
    | spl14_12 ),
    inference(avatar_split_clause,[],[f54,f141,f118])).

fof(f54,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f139,plain,
    ( spl14_7
    | spl14_11 ),
    inference(avatar_split_clause,[],[f55,f136,f118])).

fof(f55,plain,
    ( v3_pre_topc(sK5,sK2)
    | m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f134,plain,
    ( spl14_7
    | spl14_10 ),
    inference(avatar_split_clause,[],[f56,f131,f118])).

fof(f56,plain,
    ( r1_tarski(sK5,sK4)
    | m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f129,plain,
    ( spl14_7
    | spl14_9 ),
    inference(avatar_split_clause,[],[f57,f126,f118])).

fof(f57,plain,
    ( r2_hidden(sK3,sK5)
    | m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,
    ( ~ spl14_7
    | spl14_8 ),
    inference(avatar_split_clause,[],[f58,f122,f118])).

fof(f58,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK3,X3)
      | ~ r1_tarski(X3,sK4)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_connsp_2(sK4,sK2,sK3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f104,plain,
    ( spl14_1
    | spl14_3 ),
    inference(avatar_split_clause,[],[f91,f102,f94])).

fof(f94,plain,
    ( spl14_1
  <=> sP13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f91,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP12(X0)
      | sP13 ) ),
    inference(cnf_transformation,[],[f91_D])).

fof(f91_D,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ sP12(X0) )
  <=> ~ sP13 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP13])])).

fof(f100,plain,
    ( ~ spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f92,f98,f94])).

fof(f92,plain,(
    ! [X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ sP13 ) ),
    inference(general_splitting,[],[f90,f91_D])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP12(X0) ) ),
    inference(general_splitting,[],[f80,f89_D])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (2231)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (2241)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (2234)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.50  % (2228)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (2224)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (2226)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (2232)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (2235)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (2225)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (2236)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (2242)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (2243)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (2245)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (2230)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (2238)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.53  % (2247)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.53  % (2233)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.53  % (2240)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.53  % (2237)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.53  % (2252)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.53  % (2246)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (2244)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.54  % (2227)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.54  % (2229)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.55  % (2230)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f482,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f100,f104,f124,f129,f134,f139,f144,f149,f154,f159,f164,f169,f175,f181,f188,f212,f218,f237,f258,f274,f283,f301,f302,f325,f349,f416,f451,f458,f481])).
% 0.21/0.55  fof(f481,plain,(
% 0.21/0.55    spl14_53 | ~spl14_22 | ~spl14_32),
% 0.21/0.55    inference(avatar_split_clause,[],[f460,f279,f210,f455])).
% 0.21/0.55  fof(f455,plain,(
% 0.21/0.55    spl14_53 <=> sP1(sK2,k1_tops_1(sK2,sK4))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_53])])).
% 0.21/0.55  fof(f210,plain,(
% 0.21/0.55    spl14_22 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).
% 0.21/0.55  fof(f279,plain,(
% 0.21/0.55    spl14_32 <=> m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).
% 0.21/0.55  fof(f460,plain,(
% 0.21/0.55    sP1(sK2,k1_tops_1(sK2,sK4)) | (~spl14_22 | ~spl14_32)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f280,f211])).
% 0.21/0.55  fof(f211,plain,(
% 0.21/0.55    ( ! [X0] : (sP1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl14_22),
% 0.21/0.55    inference(avatar_component_clause,[],[f210])).
% 0.21/0.55  fof(f280,plain,(
% 0.21/0.55    m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl14_32),
% 0.21/0.55    inference(avatar_component_clause,[],[f279])).
% 0.21/0.55  fof(f458,plain,(
% 0.21/0.55    ~spl14_53 | ~spl14_26 | spl14_52),
% 0.21/0.55    inference(avatar_split_clause,[],[f453,f448,f234,f455])).
% 0.21/0.55  fof(f234,plain,(
% 0.21/0.55    spl14_26 <=> v3_pre_topc(k1_tops_1(sK2,sK4),sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).
% 0.21/0.55  fof(f448,plain,(
% 0.21/0.55    spl14_52 <=> sP0(k1_tops_1(sK2,sK4),sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_52])])).
% 0.21/0.55  fof(f453,plain,(
% 0.21/0.55    ~sP1(sK2,k1_tops_1(sK2,sK4)) | (~spl14_26 | spl14_52)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f236,f450,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~sP1(X0,X1) | ~v3_pre_topc(X1,X0) | sP0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X0,X1] : (((v3_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1] : ((v3_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.55  fof(f450,plain,(
% 0.21/0.55    ~sP0(k1_tops_1(sK2,sK4),sK2) | spl14_52),
% 0.21/0.55    inference(avatar_component_clause,[],[f448])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    v3_pre_topc(k1_tops_1(sK2,sK4),sK2) | ~spl14_26),
% 0.21/0.55    inference(avatar_component_clause,[],[f234])).
% 0.21/0.55  fof(f451,plain,(
% 0.21/0.55    ~spl14_52 | ~spl14_11 | ~spl14_12 | ~spl14_39 | ~spl14_48),
% 0.21/0.55    inference(avatar_split_clause,[],[f446,f413,f346,f141,f136,f448])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    spl14_11 <=> v3_pre_topc(sK5,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    spl14_12 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).
% 0.21/0.55  fof(f346,plain,(
% 0.21/0.55    spl14_39 <=> r1_tarski(sK5,k1_tops_1(sK2,sK4))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_39])])).
% 0.21/0.55  fof(f413,plain,(
% 0.21/0.55    spl14_48 <=> sP9(k1_tops_1(sK2,sK4),sK5)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_48])])).
% 0.21/0.55  fof(f446,plain,(
% 0.21/0.55    ~sP0(k1_tops_1(sK2,sK4),sK2) | (~spl14_11 | ~spl14_12 | ~spl14_39 | ~spl14_48)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f138,f143,f348,f415,f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X6,X0,X1] : (~sP0(X0,X1) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X6,X0) | ~sP9(X0,X6)) )),
% 0.21/0.55    inference(general_splitting,[],[f65,f83_D])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X6,X0,X5] : (sP9(X0,X6) | ~r2_hidden(X5,X6) | r2_hidden(X5,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f83_D])).
% 0.21/0.55  fof(f83_D,plain,(
% 0.21/0.55    ( ! [X6,X0] : (( ! [X5] : (~r2_hidden(X5,X6) | r2_hidden(X5,X0)) ) <=> ~sP9(X0,X6)) )),
% 0.21/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X0) | ~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (~r2_hidden(sK6(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK6(X0,X1),X0)) & ((r2_hidden(sK6(X0,X1),sK7(X0,X1)) & r1_tarski(sK7(X0,X1),X0) & v3_pre_topc(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK6(X0,X1),X0)))) & (! [X5] : ((r2_hidden(X5,X0) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((r2_hidden(X5,sK8(X0,X1,X5)) & r1_tarski(sK8(X0,X1,X5),X0) & v3_pre_topc(sK8(X0,X1,X5),X1) & m1_subset_1(sK8(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,X0))) | ~sP0(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f42,f45,f44,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,X0)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,X0))) => ((! [X3] : (~r2_hidden(sK6(X0,X1),X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK6(X0,X1),X0)) & (? [X4] : (r2_hidden(sK6(X0,X1),X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK6(X0,X1),X0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X4] : (r2_hidden(sK6(X0,X1),X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (r2_hidden(sK6(X0,X1),sK7(X0,X1)) & r1_tarski(sK7(X0,X1),X0) & v3_pre_topc(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ! [X5,X1,X0] : (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X0) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (r2_hidden(X5,sK8(X0,X1,X5)) & r1_tarski(sK8(X0,X1,X5),X0) & v3_pre_topc(sK8(X0,X1,X5),X1) & m1_subset_1(sK8(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,X0)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X0) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,X0)))) & (! [X5] : ((r2_hidden(X5,X0) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X0) | ~v3_pre_topc(X6,X1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X0) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,X0))) | ~sP0(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1))) | ~sP0(X1,X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.55  fof(f415,plain,(
% 0.21/0.55    sP9(k1_tops_1(sK2,sK4),sK5) | ~spl14_48),
% 0.21/0.55    inference(avatar_component_clause,[],[f413])).
% 0.21/0.55  fof(f348,plain,(
% 0.21/0.55    r1_tarski(sK5,k1_tops_1(sK2,sK4)) | ~spl14_39),
% 0.21/0.55    inference(avatar_component_clause,[],[f346])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl14_12),
% 0.21/0.55    inference(avatar_component_clause,[],[f141])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    v3_pre_topc(sK5,sK2) | ~spl14_11),
% 0.21/0.55    inference(avatar_component_clause,[],[f136])).
% 0.21/0.55  fof(f416,plain,(
% 0.21/0.55    spl14_48 | ~spl14_9 | spl14_28),
% 0.21/0.55    inference(avatar_split_clause,[],[f411,f255,f126,f413])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    spl14_9 <=> r2_hidden(sK3,sK5)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).
% 0.21/0.55  fof(f255,plain,(
% 0.21/0.55    spl14_28 <=> r2_hidden(sK3,k1_tops_1(sK2,sK4))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).
% 0.21/0.55  fof(f411,plain,(
% 0.21/0.55    sP9(k1_tops_1(sK2,sK4),sK5) | (~spl14_9 | spl14_28)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f128,f256,f83])).
% 0.21/0.55  fof(f256,plain,(
% 0.21/0.55    ~r2_hidden(sK3,k1_tops_1(sK2,sK4)) | spl14_28),
% 0.21/0.55    inference(avatar_component_clause,[],[f255])).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    r2_hidden(sK3,sK5) | ~spl14_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f126])).
% 0.21/0.55  fof(f349,plain,(
% 0.21/0.55    spl14_39 | ~spl14_10 | ~spl14_12 | ~spl14_13 | ~spl14_15 | ~spl14_37),
% 0.21/0.55    inference(avatar_split_clause,[],[f344,f322,f156,f146,f141,f131,f346])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    spl14_10 <=> r1_tarski(sK5,sK4)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).
% 0.21/0.55  fof(f146,plain,(
% 0.21/0.55    spl14_13 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).
% 0.21/0.55  fof(f156,plain,(
% 0.21/0.55    spl14_15 <=> l1_pre_topc(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).
% 0.21/0.55  fof(f322,plain,(
% 0.21/0.55    spl14_37 <=> sK5 = k1_tops_1(sK2,sK5)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_37])])).
% 0.21/0.55  fof(f344,plain,(
% 0.21/0.55    r1_tarski(sK5,k1_tops_1(sK2,sK4)) | (~spl14_10 | ~spl14_12 | ~spl14_13 | ~spl14_15 | ~spl14_37)),
% 0.21/0.55    inference(forward_demodulation,[],[f331,f324])).
% 0.21/0.55  fof(f324,plain,(
% 0.21/0.55    sK5 = k1_tops_1(sK2,sK5) | ~spl14_37),
% 0.21/0.55    inference(avatar_component_clause,[],[f322])).
% 0.21/0.55  fof(f331,plain,(
% 0.21/0.55    r1_tarski(k1_tops_1(sK2,sK5),k1_tops_1(sK2,sK4)) | (~spl14_10 | ~spl14_12 | ~spl14_13 | ~spl14_15)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f158,f133,f148,f143,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl14_13),
% 0.21/0.55    inference(avatar_component_clause,[],[f146])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    r1_tarski(sK5,sK4) | ~spl14_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f131])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    l1_pre_topc(sK2) | ~spl14_15),
% 0.21/0.55    inference(avatar_component_clause,[],[f156])).
% 0.21/0.55  fof(f325,plain,(
% 0.21/0.55    spl14_37 | ~spl14_12 | ~spl14_2 | ~spl14_11 | ~spl14_15),
% 0.21/0.55    inference(avatar_split_clause,[],[f320,f156,f136,f98,f141,f322])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    spl14_2 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 0.21/0.55  fof(f320,plain,(
% 0.21/0.55    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | sK5 = k1_tops_1(sK2,sK5) | (~spl14_2 | ~spl14_11 | ~spl14_15)),
% 0.21/0.55    inference(resolution,[],[f138,f245])).
% 0.21/0.55  fof(f245,plain,(
% 0.21/0.55    ( ! [X0] : (~v3_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_tops_1(sK2,X0) = X0) ) | (~spl14_2 | ~spl14_15)),
% 0.21/0.55    inference(resolution,[],[f99,f158])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ( ! [X3,X1] : (~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1)) ) | ~spl14_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f98])).
% 0.21/0.55  fof(f302,plain,(
% 0.21/0.55    spl14_7 | ~spl14_13 | ~spl14_14 | ~spl14_15 | ~spl14_16 | spl14_17 | ~spl14_28),
% 0.21/0.55    inference(avatar_split_clause,[],[f276,f255,f166,f161,f156,f151,f146,f118])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    spl14_7 <=> m1_connsp_2(sK4,sK2,sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    spl14_14 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    spl14_16 <=> v2_pre_topc(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    spl14_17 <=> v2_struct_0(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).
% 0.21/0.55  fof(f276,plain,(
% 0.21/0.55    m1_connsp_2(sK4,sK2,sK3) | (~spl14_13 | ~spl14_14 | ~spl14_15 | ~spl14_16 | spl14_17 | ~spl14_28)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f168,f163,f158,f153,f148,f257,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.55  fof(f257,plain,(
% 0.21/0.55    r2_hidden(sK3,k1_tops_1(sK2,sK4)) | ~spl14_28),
% 0.21/0.55    inference(avatar_component_clause,[],[f255])).
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    m1_subset_1(sK3,u1_struct_0(sK2)) | ~spl14_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f151])).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    v2_pre_topc(sK2) | ~spl14_16),
% 0.21/0.55    inference(avatar_component_clause,[],[f161])).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    ~v2_struct_0(sK2) | spl14_17),
% 0.21/0.55    inference(avatar_component_clause,[],[f166])).
% 0.21/0.55  fof(f301,plain,(
% 0.21/0.55    spl14_32 | ~spl14_31),
% 0.21/0.55    inference(avatar_split_clause,[],[f300,f271,f279])).
% 0.21/0.55  fof(f271,plain,(
% 0.21/0.55    spl14_31 <=> r1_tarski(k1_tops_1(sK2,sK4),u1_struct_0(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_31])])).
% 0.21/0.55  fof(f300,plain,(
% 0.21/0.55    m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl14_31),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f273,f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f273,plain,(
% 0.21/0.55    r1_tarski(k1_tops_1(sK2,sK4),u1_struct_0(sK2)) | ~spl14_31),
% 0.21/0.55    inference(avatar_component_clause,[],[f271])).
% 0.21/0.55  fof(f283,plain,(
% 0.21/0.55    ~spl14_23 | ~spl14_26 | ~spl14_32 | ~spl14_8 | ~spl14_28),
% 0.21/0.55    inference(avatar_split_clause,[],[f277,f255,f122,f279,f234,f215])).
% 0.21/0.55  fof(f215,plain,(
% 0.21/0.55    spl14_23 <=> r1_tarski(k1_tops_1(sK2,sK4),sK4)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_23])])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    spl14_8 <=> ! [X3] : (~r2_hidden(sK3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK4))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).
% 0.21/0.55  fof(f277,plain,(
% 0.21/0.55    ~m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(k1_tops_1(sK2,sK4),sK2) | ~r1_tarski(k1_tops_1(sK2,sK4),sK4) | (~spl14_8 | ~spl14_28)),
% 0.21/0.55    inference(resolution,[],[f257,f123])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    ( ! [X3] : (~r2_hidden(sK3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK4)) ) | ~spl14_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f122])).
% 0.21/0.55  fof(f274,plain,(
% 0.21/0.55    spl14_31 | ~spl14_19 | ~spl14_23),
% 0.21/0.55    inference(avatar_split_clause,[],[f263,f215,f178,f271])).
% 0.21/0.55  fof(f178,plain,(
% 0.21/0.55    spl14_19 <=> r1_tarski(sK4,u1_struct_0(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).
% 0.21/0.55  fof(f263,plain,(
% 0.21/0.55    r1_tarski(k1_tops_1(sK2,sK4),u1_struct_0(sK2)) | (~spl14_19 | ~spl14_23)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f180,f217,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.55  fof(f217,plain,(
% 0.21/0.55    r1_tarski(k1_tops_1(sK2,sK4),sK4) | ~spl14_23),
% 0.21/0.55    inference(avatar_component_clause,[],[f215])).
% 0.21/0.55  fof(f180,plain,(
% 0.21/0.55    r1_tarski(sK4,u1_struct_0(sK2)) | ~spl14_19),
% 0.21/0.55    inference(avatar_component_clause,[],[f178])).
% 0.21/0.55  fof(f258,plain,(
% 0.21/0.55    spl14_28 | ~spl14_7 | ~spl14_13 | ~spl14_14 | ~spl14_15 | ~spl14_16 | spl14_17),
% 0.21/0.55    inference(avatar_split_clause,[],[f252,f166,f161,f156,f151,f146,f118,f255])).
% 0.21/0.55  fof(f252,plain,(
% 0.21/0.55    r2_hidden(sK3,k1_tops_1(sK2,sK4)) | (~spl14_7 | ~spl14_13 | ~spl14_14 | ~spl14_15 | ~spl14_16 | spl14_17)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f168,f163,f158,f119,f153,f148,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f47])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    m1_connsp_2(sK4,sK2,sK3) | ~spl14_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f118])).
% 0.21/0.55  fof(f237,plain,(
% 0.21/0.55    spl14_26 | ~spl14_13 | ~spl14_15 | ~spl14_16),
% 0.21/0.55    inference(avatar_split_clause,[],[f232,f161,f156,f146,f234])).
% 0.21/0.55  fof(f232,plain,(
% 0.21/0.55    v3_pre_topc(k1_tops_1(sK2,sK4),sK2) | (~spl14_13 | ~spl14_15 | ~spl14_16)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f163,f158,f148,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.55  fof(f218,plain,(
% 0.21/0.55    spl14_23 | ~spl14_13 | ~spl14_15),
% 0.21/0.55    inference(avatar_split_clause,[],[f213,f156,f146,f215])).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    r1_tarski(k1_tops_1(sK2,sK4),sK4) | (~spl14_13 | ~spl14_15)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f158,f148,f78])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.55  fof(f212,plain,(
% 0.21/0.55    ~spl14_16 | spl14_22 | ~spl14_15),
% 0.21/0.55    inference(avatar_split_clause,[],[f203,f156,f210,f161])).
% 0.21/0.55  fof(f203,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0) | ~v2_pre_topc(sK2)) ) | ~spl14_15),
% 0.21/0.55    inference(resolution,[],[f71,f158])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1) | ~v2_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(definition_folding,[],[f15,f30,f29])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_1)).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    spl14_18 | ~spl14_13),
% 0.21/0.55    inference(avatar_split_clause,[],[f183,f146,f172])).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    spl14_18 <=> sP12(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).
% 0.21/0.55  fof(f183,plain,(
% 0.21/0.55    sP12(sK2) | ~spl14_13),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f148,f89])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    ( ! [X2,X0] : (sP12(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f89_D])).
% 0.21/0.55  fof(f89_D,plain,(
% 0.21/0.55    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) <=> ~sP12(X0)) )),
% 0.21/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP12])])).
% 0.21/0.55  fof(f181,plain,(
% 0.21/0.55    spl14_19 | ~spl14_13),
% 0.21/0.55    inference(avatar_split_clause,[],[f176,f146,f178])).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    r1_tarski(sK4,u1_struct_0(sK2)) | ~spl14_13),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f148,f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f48])).
% 0.21/0.55  fof(f175,plain,(
% 0.21/0.55    ~spl14_18 | ~spl14_3 | ~spl14_15 | ~spl14_16),
% 0.21/0.55    inference(avatar_split_clause,[],[f170,f161,f156,f102,f172])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    spl14_3 <=> ! [X0] : (~l1_pre_topc(X0) | ~sP12(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    ~sP12(sK2) | (~spl14_3 | ~spl14_15 | ~spl14_16)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f163,f158,f103])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    ( ! [X0] : (~sP12(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl14_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f102])).
% 0.21/0.55  fof(f169,plain,(
% 0.21/0.55    ~spl14_17),
% 0.21/0.55    inference(avatar_split_clause,[],[f49,f166])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ~v2_struct_0(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    (((! [X3] : (~r2_hidden(sK3,X3) | ~r1_tarski(X3,sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | ~m1_connsp_2(sK4,sK2,sK3)) & ((r2_hidden(sK3,sK5) & r1_tarski(sK5,sK4) & v3_pre_topc(sK5,sK2) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))) | m1_connsp_2(sK4,sK2,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f34,f38,f37,f36,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | ~m1_connsp_2(X2,sK2,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) | m1_connsp_2(X2,sK2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | ~m1_connsp_2(X2,sK2,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) | m1_connsp_2(X2,sK2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : ((! [X3] : (~r2_hidden(sK3,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | ~m1_connsp_2(X2,sK2,sK3)) & (? [X4] : (r2_hidden(sK3,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) | m1_connsp_2(X2,sK2,sK3)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ? [X2] : ((! [X3] : (~r2_hidden(sK3,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | ~m1_connsp_2(X2,sK2,sK3)) & (? [X4] : (r2_hidden(sK3,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) | m1_connsp_2(X2,sK2,sK3)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) => ((! [X3] : (~r2_hidden(sK3,X3) | ~r1_tarski(X3,sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | ~m1_connsp_2(sK4,sK2,sK3)) & (? [X4] : (r2_hidden(sK3,X4) & r1_tarski(X4,sK4) & v3_pre_topc(X4,sK2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) | m1_connsp_2(sK4,sK2,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ? [X4] : (r2_hidden(sK3,X4) & r1_tarski(X4,sK4) & v3_pre_topc(X4,sK2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) => (r2_hidden(sK3,sK5) & r1_tarski(sK5,sK4) & v3_pre_topc(sK5,sK2) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(rectify,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.55    inference(negated_conjecture,[],[f10])).
% 0.21/0.55  fof(f10,conjecture,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    spl14_16),
% 0.21/0.55    inference(avatar_split_clause,[],[f50,f161])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    v2_pre_topc(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    spl14_15),
% 0.21/0.55    inference(avatar_split_clause,[],[f51,f156])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    l1_pre_topc(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f154,plain,(
% 0.21/0.55    spl14_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f52,f151])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    spl14_13),
% 0.21/0.55    inference(avatar_split_clause,[],[f53,f146])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f144,plain,(
% 0.21/0.55    spl14_7 | spl14_12),
% 0.21/0.55    inference(avatar_split_clause,[],[f54,f141,f118])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | m1_connsp_2(sK4,sK2,sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    spl14_7 | spl14_11),
% 0.21/0.55    inference(avatar_split_clause,[],[f55,f136,f118])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    v3_pre_topc(sK5,sK2) | m1_connsp_2(sK4,sK2,sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    spl14_7 | spl14_10),
% 1.56/0.55    inference(avatar_split_clause,[],[f56,f131,f118])).
% 1.56/0.55  fof(f56,plain,(
% 1.56/0.55    r1_tarski(sK5,sK4) | m1_connsp_2(sK4,sK2,sK3)),
% 1.56/0.55    inference(cnf_transformation,[],[f39])).
% 1.56/0.55  fof(f129,plain,(
% 1.56/0.55    spl14_7 | spl14_9),
% 1.56/0.55    inference(avatar_split_clause,[],[f57,f126,f118])).
% 1.56/0.55  fof(f57,plain,(
% 1.56/0.55    r2_hidden(sK3,sK5) | m1_connsp_2(sK4,sK2,sK3)),
% 1.56/0.55    inference(cnf_transformation,[],[f39])).
% 1.56/0.55  fof(f124,plain,(
% 1.56/0.55    ~spl14_7 | spl14_8),
% 1.56/0.55    inference(avatar_split_clause,[],[f58,f122,f118])).
% 1.56/0.55  fof(f58,plain,(
% 1.56/0.55    ( ! [X3] : (~r2_hidden(sK3,X3) | ~r1_tarski(X3,sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_connsp_2(sK4,sK2,sK3)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f39])).
% 1.56/0.55  fof(f104,plain,(
% 1.56/0.55    spl14_1 | spl14_3),
% 1.56/0.55    inference(avatar_split_clause,[],[f91,f102,f94])).
% 1.56/0.55  fof(f94,plain,(
% 1.56/0.55    spl14_1 <=> sP13),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 1.56/0.55  fof(f91,plain,(
% 1.56/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP12(X0) | sP13) )),
% 1.56/0.55    inference(cnf_transformation,[],[f91_D])).
% 1.56/0.55  fof(f91_D,plain,(
% 1.56/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP12(X0)) ) <=> ~sP13),
% 1.56/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP13])])).
% 1.56/0.55  fof(f100,plain,(
% 1.56/0.55    ~spl14_1 | spl14_2),
% 1.56/0.55    inference(avatar_split_clause,[],[f92,f98,f94])).
% 1.56/0.55  fof(f92,plain,(
% 1.56/0.55    ( ! [X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~sP13) )),
% 1.56/0.55    inference(general_splitting,[],[f90,f91_D])).
% 1.56/0.55  fof(f90,plain,(
% 1.56/0.55    ( ! [X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP12(X0)) )),
% 1.56/0.55    inference(general_splitting,[],[f80,f89_D])).
% 1.56/0.55  fof(f80,plain,(
% 1.56/0.55    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f26])).
% 1.56/0.55  fof(f26,plain,(
% 1.56/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.56/0.55    inference(flattening,[],[f25])).
% 1.56/0.55  fof(f25,plain,(
% 1.56/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.56/0.55    inference(ennf_transformation,[],[f6])).
% 1.56/0.55  fof(f6,axiom,(
% 1.56/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 1.56/0.55  % SZS output end Proof for theBenchmark
% 1.56/0.55  % (2230)------------------------------
% 1.56/0.55  % (2230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.55  % (2230)Termination reason: Refutation
% 1.56/0.55  
% 1.56/0.55  % (2230)Memory used [KB]: 11001
% 1.56/0.55  % (2230)Time elapsed: 0.148 s
% 1.56/0.55  % (2230)------------------------------
% 1.56/0.55  % (2230)------------------------------
% 1.56/0.55  % (2223)Success in time 0.198 s
%------------------------------------------------------------------------------
