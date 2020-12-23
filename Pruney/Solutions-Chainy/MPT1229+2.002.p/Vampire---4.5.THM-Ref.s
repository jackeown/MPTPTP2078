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
% DateTime   : Thu Dec  3 13:10:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 621 expanded)
%              Number of leaves         :   37 ( 302 expanded)
%              Depth                    :   11
%              Number of atoms          :  584 (3519 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f86,f91,f97,f103,f109,f117,f118,f124,f134,f139,f140,f145,f153,f165,f170,f175,f176,f181,f186,f191,f198,f204,f210,f217,f218])).

fof(f218,plain,
    ( ~ spl6_26
    | spl6_1
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f211,f142,f83,f58,f214])).

fof(f214,plain,
    ( spl6_26
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f58,plain,
    ( spl6_1
  <=> v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f83,plain,
    ( spl6_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f142,plain,
    ( spl6_15
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f211,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f85,f60,f144,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f144,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_pre_topc(sK0))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f60,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f85,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f217,plain,
    ( spl6_26
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f212,f142,f94,f214])).

fof(f94,plain,
    ( spl6_8
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f212,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f96,f144,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

% (23750)WARNING: option uwaf not known.
fof(f96,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f210,plain,
    ( spl6_25
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f205,f136,f94,f207])).

fof(f207,plain,
    ( spl6_25
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f136,plain,
    ( spl6_14
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f205,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f96,f138,f56])).

fof(f138,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK1),u1_pre_topc(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f204,plain,
    ( spl6_24
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f199,f131,f94,f201])).

fof(f201,plain,
    ( spl6_24
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f131,plain,
    ( spl6_13
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f199,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(unit_resulting_resolution,[],[f96,f133,f56])).

fof(f133,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK1),u1_pre_topc(sK0))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f198,plain,
    ( spl6_23
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f193,f114,f94,f195])).

fof(f195,plain,
    ( spl6_23
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f114,plain,
    ( spl6_11
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK2),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f193,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f96,f116,f56])).

fof(f116,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK2),u1_pre_topc(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f191,plain,
    ( spl6_22
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f154,f150,f100,f83,f188])).

fof(f188,plain,
    ( spl6_22
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f100,plain,
    ( spl6_9
  <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f150,plain,
    ( spl6_16
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f154,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f85,f102,f152,f55])).

fof(f152,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f102,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f186,plain,
    ( spl6_21
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f155,f150,f106,f100,f88,f83,f73,f183])).

fof(f183,plain,
    ( spl6_21
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f73,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f88,plain,
    ( spl6_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f106,plain,
    ( spl6_10
  <=> r2_hidden(sK2,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f155,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2),u1_pre_topc(sK0))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f85,f90,f108,f75,f102,f152,f38])).

fof(f38,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0))
            & r2_hidden(sK4(X0),u1_pre_topc(X0))
            & r2_hidden(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
            & r1_tarski(sK5(X0),u1_pre_topc(X0))
            & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                    | ~ r2_hidden(X5,u1_pre_topc(X0))
                    | ~ r2_hidden(X4,u1_pre_topc(X0))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X6] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
                | ~ r1_tarski(X6,u1_pre_topc(X0))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK3(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0))
        & r2_hidden(sK4(X0),u1_pre_topc(X0))
        & r2_hidden(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
        & r1_tarski(sK5(X0),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                    | ~ r2_hidden(X5,u1_pre_topc(X0))
                    | ~ r2_hidden(X4,u1_pre_topc(X0))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X6] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
                | ~ r1_tarski(X6,u1_pre_topc(X0))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X1] :
                ( ! [X2] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                    | ~ r2_hidden(X2,u1_pre_topc(X0))
                    | ~ r2_hidden(X1,u1_pre_topc(X0))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X1] :
                ( ! [X2] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                    | ~ r2_hidden(X2,u1_pre_topc(X0))
                    | ~ r2_hidden(X1,u1_pre_topc(X0))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f108,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f90,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f181,plain,
    ( spl6_20
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f156,f150,f121,f100,f88,f83,f78,f178])).

fof(f178,plain,
    ( spl6_20
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f78,plain,
    ( spl6_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f121,plain,
    ( spl6_12
  <=> r2_hidden(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f156,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f85,f90,f123,f80,f102,f152,f38])).

fof(f80,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f123,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f176,plain,
    ( spl6_17
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f157,f150,f100,f88,f83,f162])).

fof(f162,plain,
    ( spl6_17
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f157,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)),u1_pre_topc(sK0))
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f85,f90,f102,f152,f102,f152,f38])).

fof(f175,plain,
    ( spl6_19
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f158,f150,f106,f100,f88,f83,f73,f172])).

fof(f172,plain,
    ( spl6_19
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f158,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_pre_topc(sK0))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f85,f90,f108,f75,f102,f152,f38])).

fof(f170,plain,
    ( spl6_18
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f159,f150,f121,f100,f88,f83,f78,f167])).

fof(f167,plain,
    ( spl6_18
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f159,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_pre_topc(sK0))
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f85,f90,f123,f80,f102,f152,f38])).

fof(f165,plain,
    ( spl6_17
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f160,f150,f100,f88,f83,f162])).

fof(f160,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)),u1_pre_topc(sK0))
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f85,f90,f102,f152,f102,f152,f38])).

fof(f153,plain,
    ( spl6_16
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f148,f100,f94,f150])).

fof(f148,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f102,f96,f56])).

fof(f145,plain,
    ( spl6_15
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f126,f121,f106,f88,f83,f78,f73,f142])).

fof(f126,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_pre_topc(sK0))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f85,f90,f108,f75,f80,f123,f38])).

fof(f140,plain,
    ( spl6_13
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f127,f121,f88,f83,f78,f131])).

fof(f127,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK1),u1_pre_topc(sK0))
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f85,f90,f123,f80,f80,f123,f38])).

fof(f139,plain,
    ( spl6_14
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f128,f121,f106,f88,f83,f78,f73,f136])).

fof(f128,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK1),u1_pre_topc(sK0))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f85,f90,f108,f75,f80,f123,f38])).

fof(f134,plain,
    ( spl6_13
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f129,f121,f88,f83,f78,f131])).

fof(f129,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK1),u1_pre_topc(sK0))
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f85,f90,f123,f80,f80,f123,f38])).

fof(f124,plain,
    ( spl6_12
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f119,f83,f78,f68,f121])).

fof(f68,plain,
    ( spl6_3
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f119,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f85,f70,f80,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f118,plain,
    ( spl6_11
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f111,f106,f88,f83,f73,f114])).

fof(f111,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK2),u1_pre_topc(sK0))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f85,f90,f108,f75,f75,f108,f38])).

fof(f117,plain,
    ( spl6_11
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f112,f106,f88,f83,f73,f114])).

fof(f112,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK2),u1_pre_topc(sK0))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f85,f90,f108,f75,f75,f108,f38])).

fof(f109,plain,
    ( spl6_10
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f104,f83,f73,f63,f106])).

fof(f63,plain,
    ( spl6_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f104,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK0))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f85,f65,f75,f54])).

fof(f65,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f103,plain,
    ( spl6_9
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f98,f88,f83,f100])).

fof(f98,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f85,f90,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f97,plain,
    ( spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f92,f83,f94])).

fof(f92,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f85,f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f91,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f28,f88])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v3_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v3_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v3_pre_topc(X2,sK0)
            & v3_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v3_pre_topc(X2,sK0)
          & v3_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v3_pre_topc(X2,sK0)
        & v3_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v3_pre_topc(sK2,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

% (23755)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v3_pre_topc(X1,X0) )
               => v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_1)).

fof(f86,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f29,f83])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f30,f78])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f32,f68])).

fof(f32,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f33,f63])).

fof(f33,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:21:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (23753)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (23740)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (23753)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f86,f91,f97,f103,f109,f117,f118,f124,f134,f139,f140,f145,f153,f165,f170,f175,f176,f181,f186,f191,f198,f204,f210,f217,f218])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    ~spl6_26 | spl6_1 | ~spl6_6 | ~spl6_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f211,f142,f83,f58,f214])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    spl6_26 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl6_1 <=> v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl6_6 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl6_15 <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_pre_topc(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_6 | ~spl6_15)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f85,f60,f144,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_pre_topc(sK0)) | ~spl6_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f142])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl6_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl6_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f83])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    spl6_26 | ~spl6_8 | ~spl6_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f212,f142,f94,f214])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl6_8 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_8 | ~spl6_15)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f96,f144,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  % (23750)WARNING: option uwaf not known.
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f94])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    spl6_25 | ~spl6_8 | ~spl6_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f205,f136,f94,f207])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    spl6_25 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl6_14 <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK1),u1_pre_topc(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_8 | ~spl6_14)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f96,f138,f56])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK1),u1_pre_topc(sK0)) | ~spl6_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f136])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    spl6_24 | ~spl6_8 | ~spl6_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f199,f131,f94,f201])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    spl6_24 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl6_13 <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK1),u1_pre_topc(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_8 | ~spl6_13)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f96,f133,f56])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK1),u1_pre_topc(sK0)) | ~spl6_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f131])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    spl6_23 | ~spl6_8 | ~spl6_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f193,f114,f94,f195])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    spl6_23 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl6_11 <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK2),u1_pre_topc(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_8 | ~spl6_11)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f96,f116,f56])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK2),u1_pre_topc(sK0)) | ~spl6_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f114])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    spl6_22 | ~spl6_6 | ~spl6_9 | ~spl6_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f154,f150,f100,f83,f188])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    spl6_22 <=> v3_pre_topc(u1_struct_0(sK0),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl6_9 <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    spl6_16 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    v3_pre_topc(u1_struct_0(sK0),sK0) | (~spl6_6 | ~spl6_9 | ~spl6_16)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f85,f102,f152,f55])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f150])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~spl6_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    spl6_21 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f155,f150,f106,f100,f88,f83,f73,f183])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    spl6_21 <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2),u1_pre_topc(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl6_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl6_7 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl6_10 <=> r2_hidden(sK2,u1_pre_topc(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2),u1_pre_topc(sK0)) | (~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_16)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f85,f90,f108,f75,f102,f152,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X4,X0,X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (((v2_pre_topc(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (((v2_pre_topc(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(rectify,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (((v2_pre_topc(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (((v2_pre_topc(X0) | (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.51    inference(rectify,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f73])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    r2_hidden(sK2,u1_pre_topc(sK0)) | ~spl6_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f106])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    v2_pre_topc(sK0) | ~spl6_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f88])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    spl6_20 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_12 | ~spl6_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f156,f150,f121,f100,f88,f83,f78,f178])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    spl6_20 <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_pre_topc(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl6_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl6_12 <=> r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f90,f123,f80,f102,f152,f38])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    r2_hidden(sK1,u1_pre_topc(sK0)) | ~spl6_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f121])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    spl6_17 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f157,f150,f100,f88,f83,f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    spl6_17 <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)),u1_pre_topc(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)),u1_pre_topc(sK0)) | (~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_16)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f90,f102,f152,f102,f152,f38])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    spl6_19 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f158,f150,f106,f100,f88,f83,f73,f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    spl6_19 <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_pre_topc(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_pre_topc(sK0)) | (~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_16)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f90,f108,f75,f102,f152,f38])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl6_18 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_12 | ~spl6_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f159,f150,f121,f100,f88,f83,f78,f167])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    spl6_18 <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_pre_topc(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_pre_topc(sK0)) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f90,f123,f80,f102,f152,f38])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    spl6_17 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f160,f150,f100,f88,f83,f162])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    r2_hidden(k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)),u1_pre_topc(sK0)) | (~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_16)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f90,f102,f152,f102,f152,f38])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl6_16 | ~spl6_8 | ~spl6_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f148,f100,f94,f150])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_8 | ~spl6_9)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f102,f96,f56])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl6_15 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_10 | ~spl6_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f126,f121,f106,f88,f83,f78,f73,f142])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_pre_topc(sK0)) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_10 | ~spl6_12)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f90,f108,f75,f80,f123,f38])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl6_13 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f127,f121,f88,f83,f78,f131])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK1),u1_pre_topc(sK0)) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_12)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f90,f123,f80,f80,f123,f38])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl6_14 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_10 | ~spl6_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f128,f121,f106,f88,f83,f78,f73,f136])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK1),u1_pre_topc(sK0)) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_10 | ~spl6_12)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f90,f108,f75,f80,f123,f38])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl6_13 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f129,f121,f88,f83,f78,f131])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK1),u1_pre_topc(sK0)) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_12)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f90,f123,f80,f80,f123,f38])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl6_12 | ~spl6_3 | ~spl6_5 | ~spl6_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f119,f83,f78,f68,f121])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl6_3 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    r2_hidden(sK1,u1_pre_topc(sK0)) | (~spl6_3 | ~spl6_5 | ~spl6_6)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f70,f80,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    v3_pre_topc(sK1,sK0) | ~spl6_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f68])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl6_11 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f111,f106,f88,f83,f73,f114])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK2),u1_pre_topc(sK0)) | (~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_10)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f90,f108,f75,f75,f108,f38])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl6_11 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f112,f106,f88,f83,f73,f114])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK2),u1_pre_topc(sK0)) | (~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_10)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f90,f108,f75,f75,f108,f38])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    spl6_10 | ~spl6_2 | ~spl6_4 | ~spl6_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f104,f83,f73,f63,f106])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl6_2 <=> v3_pre_topc(sK2,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    r2_hidden(sK2,u1_pre_topc(sK0)) | (~spl6_2 | ~spl6_4 | ~spl6_6)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f65,f75,f54])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    v3_pre_topc(sK2,sK0) | ~spl6_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl6_9 | ~spl6_6 | ~spl6_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f98,f88,f83,f100])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | (~spl6_6 | ~spl6_7)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f90,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl6_8 | ~spl6_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f92,f83,f94])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_6),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl6_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f28,f88])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ((~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (~v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X2] : (~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (~v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  % (23755)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((~v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0)) => v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0)) => v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_1)).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl6_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f83])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl6_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f78])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl6_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f73])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl6_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f32,f68])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    v3_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl6_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f63])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    v3_pre_topc(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ~spl6_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f58])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (23753)------------------------------
% 0.21/0.52  % (23753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23753)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (23749)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (23753)Memory used [KB]: 5500
% 0.21/0.52  % (23753)Time elapsed: 0.085 s
% 0.21/0.52  % (23753)------------------------------
% 0.21/0.52  % (23753)------------------------------
% 0.21/0.52  % (23745)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.52  % (23748)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (23739)Success in time 0.157 s
%------------------------------------------------------------------------------
