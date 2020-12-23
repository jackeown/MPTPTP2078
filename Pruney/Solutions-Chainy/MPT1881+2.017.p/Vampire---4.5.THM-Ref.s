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
% DateTime   : Thu Dec  3 13:21:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 345 expanded)
%              Number of leaves         :   39 ( 141 expanded)
%              Depth                    :   13
%              Number of atoms          :  651 (1385 expanded)
%              Number of equality atoms :   54 (  99 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f277,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f99,f104,f114,f116,f125,f134,f139,f144,f149,f162,f169,f185,f200,f213,f234,f246,f266,f271,f274,f276])).

fof(f276,plain,
    ( sK1 != k2_struct_0(sK0)
    | v3_tex_2(sK1,sK0)
    | ~ v3_tex_2(k2_struct_0(sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f274,plain,
    ( ~ spl3_7
    | ~ spl3_12
    | ~ spl3_13
    | spl3_14
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_13
    | spl3_14
    | ~ spl3_24 ),
    inference(unit_resulting_resolution,[],[f109,f160,f148,f143,f105,f265])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | X0 = X1 )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl3_24
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v3_tex_2(X0,sK0)
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f53,f52])).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f143,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f148,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_13
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f160,plain,
    ( sK1 != k2_struct_0(sK0)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_14
  <=> sK1 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f109,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_7
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f271,plain,
    ( spl3_25
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f262,f243,f210,f131,f89,f79,f74,f268])).

fof(f268,plain,
    ( spl3_25
  <=> v3_tex_2(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f74,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f79,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f89,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f131,plain,
    ( spl3_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f210,plain,
    ( spl3_18
  <=> v1_tops_1(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f243,plain,
    ( spl3_21
  <=> v2_tex_2(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f262,plain,
    ( v3_tex_2(k2_struct_0(sK0),sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f220,f245])).

fof(f245,plain,
    ( v2_tex_2(k2_struct_0(sK0),sK0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f243])).

fof(f220,plain,
    ( ~ v2_tex_2(k2_struct_0(sK0),sK0)
    | v3_tex_2(k2_struct_0(sK0),sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f219,f105])).

fof(f219,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v2_tex_2(k2_struct_0(sK0),sK0)
    | v3_tex_2(k2_struct_0(sK0),sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f218,f133])).

fof(f133,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f218,plain,
    ( ~ v2_tex_2(k2_struct_0(sK0),sK0)
    | v3_tex_2(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f217,f76])).

fof(f76,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f217,plain,
    ( ~ v2_tex_2(k2_struct_0(sK0),sK0)
    | v3_tex_2(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f216,f81])).

fof(f81,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f216,plain,
    ( ~ v2_tex_2(k2_struct_0(sK0),sK0)
    | v3_tex_2(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f214,f91])).

fof(f91,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f214,plain,
    ( ~ v2_tex_2(k2_struct_0(sK0),sK0)
    | v3_tex_2(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_18 ),
    inference(resolution,[],[f212,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(f212,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f210])).

fof(f266,plain,
    ( spl3_24
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f261,f232,f131,f89,f264])).

fof(f232,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f261,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v3_tex_2(X0,sK0)
        | X0 = X1 )
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f208,f233])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f232])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0)
        | ~ v3_tex_2(X0,sK0)
        | X0 = X1 )
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f207,f133])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0)
        | ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | X0 = X1 )
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f206,f133])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | X0 = X1 )
    | ~ spl3_4 ),
    inference(resolution,[],[f61,f91])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f246,plain,
    ( spl3_21
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f235,f232,f243])).

fof(f235,plain,
    ( v2_tex_2(k2_struct_0(sK0),sK0)
    | ~ spl3_20 ),
    inference(resolution,[],[f233,f105])).

fof(f234,plain,
    ( spl3_20
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f223,f131,f89,f84,f74,f232])).

fof(f84,plain,
    ( spl3_3
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f172,f133])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f171,f76])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f170,f91])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f164,f86])).

fof(f86,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f66,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f213,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f205,f197,f131,f89,f210])).

fof(f197,plain,
    ( spl3_17
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f205,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f204,f105])).

fof(f204,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f203,f133])).

fof(f203,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f202,f91])).

fof(f202,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f201,f133])).

fof(f201,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_17 ),
    inference(superposition,[],[f59,f199])).

fof(f199,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f197])).

fof(f59,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f200,plain,
    ( spl3_17
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f126,f89,f197])).

fof(f126,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f56,f91])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(f185,plain,
    ( ~ spl3_8
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f183,f93])).

fof(f93,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f51,f52])).

fof(f51,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f183,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f112,f168])).

fof(f168,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_15
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f112,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_8
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f169,plain,
    ( spl3_15
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f163,f159,f131,f166])).

fof(f163,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f133,f161])).

fof(f161,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f162,plain,
    ( spl3_14
    | spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f154,f141,f136,f159])).

fof(f136,plain,
    ( spl3_11
  <=> v1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f154,plain,
    ( sK1 = k2_struct_0(sK0)
    | spl3_11
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f153,f138])).

fof(f138,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f153,plain,
    ( sK1 = k2_struct_0(sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_12 ),
    inference(resolution,[],[f69,f143])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f149,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f127,f122,f96,f146])).

fof(f96,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f122,plain,
    ( spl3_9
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f127,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f124,f117])).

fof(f117,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f54,f98])).

fof(f98,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f124,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f144,plain,
    ( spl3_12
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f129,f101,f96,f141])).

fof(f101,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f129,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f103,f117])).

fof(f103,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f139,plain,
    ( ~ spl3_11
    | ~ spl3_5
    | spl3_8 ),
    inference(avatar_split_clause,[],[f128,f111,f96,f136])).

fof(f128,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_5
    | spl3_8 ),
    inference(backward_demodulation,[],[f113,f117])).

fof(f113,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f134,plain,
    ( spl3_10
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f117,f96,f131])).

fof(f125,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f118,f101,f122])).

fof(f118,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(resolution,[],[f70,f103])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f116,plain,
    ( ~ spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f115,f111,f107])).

fof(f115,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl3_8 ),
    inference(subsumption_resolution,[],[f50,f113])).

fof(f50,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(f114,plain,
    ( spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f49,f111,f107])).

fof(f49,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f99,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f94,f89,f96])).

fof(f94,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f55,f91])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f92,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f47,f89])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f46,f84])).

fof(f46,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f45,f79])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f44,f74])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:59:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (28200)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (28198)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (28200)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (28206)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (28221)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (28208)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (28201)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (28202)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (28198)Refutation not found, incomplete strategy% (28198)------------------------------
% 0.22/0.52  % (28198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28198)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28198)Memory used [KB]: 10618
% 0.22/0.52  % (28198)Time elapsed: 0.087 s
% 0.22/0.52  % (28198)------------------------------
% 0.22/0.52  % (28198)------------------------------
% 0.22/0.52  % (28213)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f277,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f99,f104,f114,f116,f125,f134,f139,f144,f149,f162,f169,f185,f200,f213,f234,f246,f266,f271,f274,f276])).
% 0.22/0.52  fof(f276,plain,(
% 0.22/0.52    sK1 != k2_struct_0(sK0) | v3_tex_2(sK1,sK0) | ~v3_tex_2(k2_struct_0(sK0),sK0)),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f274,plain,(
% 0.22/0.52    ~spl3_7 | ~spl3_12 | ~spl3_13 | spl3_14 | ~spl3_24),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f272])).
% 0.22/0.52  fof(f272,plain,(
% 0.22/0.52    $false | (~spl3_7 | ~spl3_12 | ~spl3_13 | spl3_14 | ~spl3_24)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f109,f160,f148,f143,f105,f265])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v3_tex_2(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | X0 = X1) ) | ~spl3_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f264])).
% 0.22/0.52  fof(f264,plain,(
% 0.22/0.52    spl3_24 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v3_tex_2(X0,sK0) | X0 = X1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f53,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f141])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    spl3_12 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl3_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f146])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    spl3_13 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    sK1 != k2_struct_0(sK0) | spl3_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f159])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    spl3_14 <=> sK1 = k2_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    v3_tex_2(sK1,sK0) | ~spl3_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f107])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    spl3_7 <=> v3_tex_2(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.52  fof(f271,plain,(
% 0.22/0.52    spl3_25 | spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_10 | ~spl3_18 | ~spl3_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f262,f243,f210,f131,f89,f79,f74,f268])).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    spl3_25 <=> v3_tex_2(k2_struct_0(sK0),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    spl3_1 <=> v2_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl3_2 <=> v2_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    spl3_4 <=> l1_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    spl3_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    spl3_18 <=> v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.52  fof(f243,plain,(
% 0.22/0.52    spl3_21 <=> v2_tex_2(k2_struct_0(sK0),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.52  fof(f262,plain,(
% 0.22/0.52    v3_tex_2(k2_struct_0(sK0),sK0) | (spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_10 | ~spl3_18 | ~spl3_21)),
% 0.22/0.52    inference(subsumption_resolution,[],[f220,f245])).
% 0.22/0.52  fof(f245,plain,(
% 0.22/0.52    v2_tex_2(k2_struct_0(sK0),sK0) | ~spl3_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f243])).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    ~v2_tex_2(k2_struct_0(sK0),sK0) | v3_tex_2(k2_struct_0(sK0),sK0) | (spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_10 | ~spl3_18)),
% 0.22/0.52    inference(subsumption_resolution,[],[f219,f105])).
% 0.22/0.52  fof(f219,plain,(
% 0.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tex_2(k2_struct_0(sK0),sK0) | v3_tex_2(k2_struct_0(sK0),sK0) | (spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_10 | ~spl3_18)),
% 0.22/0.52    inference(forward_demodulation,[],[f218,f133])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f131])).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    ~v2_tex_2(k2_struct_0(sK0),sK0) | v3_tex_2(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_18)),
% 0.22/0.52    inference(subsumption_resolution,[],[f217,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ~v2_struct_0(sK0) | spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f74])).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    ~v2_tex_2(k2_struct_0(sK0),sK0) | v3_tex_2(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl3_2 | ~spl3_4 | ~spl3_18)),
% 0.22/0.52    inference(subsumption_resolution,[],[f216,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    v2_pre_topc(sK0) | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f79])).
% 0.22/0.52  fof(f216,plain,(
% 0.22/0.52    ~v2_tex_2(k2_struct_0(sK0),sK0) | v3_tex_2(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_4 | ~spl3_18)),
% 0.22/0.52    inference(subsumption_resolution,[],[f214,f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    l1_pre_topc(sK0) | ~spl3_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f89])).
% 0.22/0.52  fof(f214,plain,(
% 0.22/0.52    ~v2_tex_2(k2_struct_0(sK0),sK0) | v3_tex_2(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_18),
% 0.22/0.52    inference(resolution,[],[f212,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 0.22/0.52  fof(f212,plain,(
% 0.22/0.52    v1_tops_1(k2_struct_0(sK0),sK0) | ~spl3_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f210])).
% 0.22/0.52  fof(f266,plain,(
% 0.22/0.52    spl3_24 | ~spl3_4 | ~spl3_10 | ~spl3_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f261,f232,f131,f89,f264])).
% 0.22/0.52  fof(f232,plain,(
% 0.22/0.52    spl3_20 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v3_tex_2(X0,sK0) | X0 = X1) ) | (~spl3_4 | ~spl3_10 | ~spl3_20)),
% 0.22/0.52    inference(subsumption_resolution,[],[f208,f233])).
% 0.22/0.52  fof(f233,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl3_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f232])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0) | ~v3_tex_2(X0,sK0) | X0 = X1) ) | (~spl3_4 | ~spl3_10)),
% 0.22/0.52    inference(forward_demodulation,[],[f207,f133])).
% 0.22/0.52  fof(f207,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0) | ~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | X0 = X1) ) | (~spl3_4 | ~spl3_10)),
% 0.22/0.52    inference(forward_demodulation,[],[f206,f133])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | X0 = X1) ) | ~spl3_4),
% 0.22/0.52    inference(resolution,[],[f61,f91])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | X1 = X3) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(rectify,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.22/0.52  fof(f246,plain,(
% 0.22/0.52    spl3_21 | ~spl3_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f235,f232,f243])).
% 0.22/0.52  fof(f235,plain,(
% 0.22/0.52    v2_tex_2(k2_struct_0(sK0),sK0) | ~spl3_20),
% 0.22/0.52    inference(resolution,[],[f233,f105])).
% 0.22/0.52  fof(f234,plain,(
% 0.22/0.52    spl3_20 | spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f223,f131,f89,f84,f74,f232])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    spl3_3 <=> v1_tdlat_3(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_10)),
% 0.22/0.52    inference(forward_demodulation,[],[f172,f133])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (spl3_1 | ~spl3_3 | ~spl3_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f171,f76])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | (~spl3_3 | ~spl3_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f170,f91])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | ~spl3_3),
% 0.22/0.52    inference(resolution,[],[f164,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    v1_tdlat_3(sK0) | ~spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f84])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_tdlat_3(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f66,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    spl3_18 | ~spl3_4 | ~spl3_10 | ~spl3_17),
% 0.22/0.52    inference(avatar_split_clause,[],[f205,f197,f131,f89,f210])).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    spl3_17 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.52  fof(f205,plain,(
% 0.22/0.52    v1_tops_1(k2_struct_0(sK0),sK0) | (~spl3_4 | ~spl3_10 | ~spl3_17)),
% 0.22/0.52    inference(subsumption_resolution,[],[f204,f105])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k2_struct_0(sK0),sK0) | (~spl3_4 | ~spl3_10 | ~spl3_17)),
% 0.22/0.52    inference(forward_demodulation,[],[f203,f133])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    v1_tops_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_4 | ~spl3_10 | ~spl3_17)),
% 0.22/0.52    inference(subsumption_resolution,[],[f202,f91])).
% 0.22/0.52  fof(f202,plain,(
% 0.22/0.52    v1_tops_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_17)),
% 0.22/0.52    inference(subsumption_resolution,[],[f201,f133])).
% 0.22/0.52  fof(f201,plain,(
% 0.22/0.52    u1_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_17),
% 0.22/0.52    inference(superposition,[],[f59,f199])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~spl3_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f197])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0,X1] : (u1_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.22/0.52  fof(f200,plain,(
% 0.22/0.52    spl3_17 | ~spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f126,f89,f197])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~spl3_4),
% 0.22/0.52    inference(resolution,[],[f56,f91])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    ~spl3_8 | ~spl3_15),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f184])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    $false | (~spl3_8 | ~spl3_15)),
% 0.22/0.52    inference(subsumption_resolution,[],[f183,f93])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.22/0.52    inference(backward_demodulation,[],[f51,f52])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    v1_subset_1(sK1,sK1) | (~spl3_8 | ~spl3_15)),
% 0.22/0.52    inference(forward_demodulation,[],[f112,f168])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    u1_struct_0(sK0) = sK1 | ~spl3_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f166])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    spl3_15 <=> u1_struct_0(sK0) = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    spl3_8 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    spl3_15 | ~spl3_10 | ~spl3_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f163,f159,f131,f166])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    u1_struct_0(sK0) = sK1 | (~spl3_10 | ~spl3_14)),
% 0.22/0.52    inference(forward_demodulation,[],[f133,f161])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    sK1 = k2_struct_0(sK0) | ~spl3_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f159])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    spl3_14 | spl3_11 | ~spl3_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f154,f141,f136,f159])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    spl3_11 <=> v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    sK1 = k2_struct_0(sK0) | (spl3_11 | ~spl3_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f153,f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ~v1_subset_1(sK1,k2_struct_0(sK0)) | spl3_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f136])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    sK1 = k2_struct_0(sK0) | v1_subset_1(sK1,k2_struct_0(sK0)) | ~spl3_12),
% 0.22/0.52    inference(resolution,[],[f69,f143])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    spl3_13 | ~spl3_5 | ~spl3_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f127,f122,f96,f146])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    spl3_5 <=> l1_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    spl3_9 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    r1_tarski(sK1,k2_struct_0(sK0)) | (~spl3_5 | ~spl3_9)),
% 0.22/0.52    inference(backward_demodulation,[],[f124,f117])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.22/0.52    inference(resolution,[],[f54,f98])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    l1_struct_0(sK0) | ~spl3_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f96])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f122])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    spl3_12 | ~spl3_5 | ~spl3_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f129,f101,f96,f141])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_5 | ~spl3_6)),
% 0.22/0.52    inference(backward_demodulation,[],[f103,f117])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f101])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ~spl3_11 | ~spl3_5 | spl3_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f128,f111,f96,f136])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ~v1_subset_1(sK1,k2_struct_0(sK0)) | (~spl3_5 | spl3_8)),
% 0.22/0.52    inference(backward_demodulation,[],[f113,f117])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl3_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f111])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    spl3_10 | ~spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f117,f96,f131])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    spl3_9 | ~spl3_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f118,f101,f122])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 0.22/0.52    inference(resolution,[],[f70,f103])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ~spl3_7 | spl3_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f115,f111,f107])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ~v3_tex_2(sK1,sK0) | spl3_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f50,f113])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f14])).
% 0.22/0.52  fof(f14,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    spl3_7 | ~spl3_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f49,f111,f107])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    spl3_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f48,f101])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    spl3_5 | ~spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f94,f89,f96])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    l1_struct_0(sK0) | ~spl3_4),
% 0.22/0.52    inference(resolution,[],[f55,f91])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f47,f89])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f46,f84])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    v1_tdlat_3(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f45,f79])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ~spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f44,f74])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (28200)------------------------------
% 0.22/0.52  % (28200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28200)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (28200)Memory used [KB]: 6268
% 0.22/0.52  % (28200)Time elapsed: 0.089 s
% 0.22/0.52  % (28200)------------------------------
% 0.22/0.52  % (28200)------------------------------
% 0.22/0.52  % (28197)Success in time 0.158 s
%------------------------------------------------------------------------------
