%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:33 EST 2020

% Result     : Theorem 3.16s
% Output     : Refutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  423 (1282 expanded)
%              Number of leaves         :   92 ( 552 expanded)
%              Depth                    :   20
%              Number of atoms          : 1980 (6923 expanded)
%              Number of equality atoms :   85 ( 405 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (25212)Refutation not found, incomplete strategy% (25212)------------------------------
% (25212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25212)Termination reason: Refutation not found, incomplete strategy

% (25212)Memory used [KB]: 6652
% (25212)Time elapsed: 0.155 s
% (25212)------------------------------
% (25212)------------------------------
fof(f4957,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f185,f186,f191,f196,f206,f211,f212,f217,f222,f227,f232,f255,f270,f286,f301,f355,f726,f772,f775,f886,f1350,f1641,f1695,f1752,f1948,f1953,f1963,f2075,f2089,f2200,f2324,f2457,f2532,f2533,f2553,f2613,f2689,f2740,f2860,f3173,f3207,f3277,f3353,f3409,f3469,f3477,f3532,f3541,f3543,f4004,f4077,f4078,f4079,f4195,f4293,f4294,f4298,f4503,f4506,f4539,f4695,f4837,f4918,f4953,f4955,f4956])).

fof(f4956,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != u1_struct_0(sK1)
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4955,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK3
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4953,plain,
    ( ~ spl8_83
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_52
    | ~ spl8_56
    | ~ spl8_57
    | ~ spl8_58
    | spl8_85
    | ~ spl8_138 ),
    inference(avatar_split_clause,[],[f4945,f2406,f1268,f680,f675,f670,f650,f229,f224,f219,f214,f1260])).

fof(f1260,plain,
    ( spl8_83
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f214,plain,
    ( spl8_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f219,plain,
    ( spl8_9
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f224,plain,
    ( spl8_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f229,plain,
    ( spl8_11
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f650,plain,
    ( spl8_52
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f670,plain,
    ( spl8_56
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f675,plain,
    ( spl8_57
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f680,plain,
    ( spl8_58
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f1268,plain,
    ( spl8_85
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).

fof(f2406,plain,
    ( spl8_138
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).

fof(f4945,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_52
    | ~ spl8_56
    | ~ spl8_57
    | ~ spl8_58
    | spl8_85
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f231,f226,f221,f216,f672,f651,f682,f677,f2667,f1270,f176])).

fof(f176,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f1270,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl8_85 ),
    inference(avatar_component_clause,[],[f1268])).

fof(f2667,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f2539,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2539,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f2515,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f84,f85])).

fof(f85,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f2515,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f105,f2407,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f2407,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_138 ),
    inference(avatar_component_clause,[],[f2406])).

fof(f105,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f677,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f675])).

fof(f682,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f680])).

fof(f651,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f650])).

fof(f672,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f670])).

fof(f216,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f214])).

fof(f221,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f219])).

fof(f226,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f224])).

fof(f231,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f229])).

fof(f4918,plain,
    ( spl8_52
    | ~ spl8_1
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f4917,f445,f178,f650])).

fof(f178,plain,
    ( spl8_1
  <=> v5_pre_topc(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f445,plain,
    ( spl8_30
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f4917,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl8_1
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f179,f447])).

fof(f447,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f445])).

fof(f179,plain,
    ( v5_pre_topc(sK3,sK0,sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f178])).

fof(f4837,plain,
    ( ~ spl8_85
    | ~ spl8_83
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_30
    | ~ spl8_40
    | ~ spl8_138 ),
    inference(avatar_split_clause,[],[f4836,f2406,f526,f445,f298,f219,f214,f198,f193,f188,f182,f1260,f1268])).

fof(f182,plain,
    ( spl8_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f188,plain,
    ( spl8_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f193,plain,
    ( spl8_4
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f198,plain,
    ( spl8_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f298,plain,
    ( spl8_15
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f526,plain,
    ( spl8_40
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f4836,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_30
    | ~ spl8_40
    | ~ spl8_138 ),
    inference(forward_demodulation,[],[f4835,f447])).

fof(f4835,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_30
    | ~ spl8_40
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f4834,f2667])).

fof(f4834,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_30
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f4833,f447])).

fof(f4833,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_30
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f4832,f447])).

fof(f4832,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f4831,f300])).

fof(f300,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f298])).

fof(f4831,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f4830,f527])).

fof(f527,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f526])).

fof(f4830,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f4829,f221])).

fof(f4829,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f1145,f216])).

fof(f1145,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f1144,f200])).

fof(f200,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f198])).

fof(f1144,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1143,f195])).

fof(f195,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f193])).

fof(f1143,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f1117,f184])).

fof(f184,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f182])).

fof(f1117,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl8_3 ),
    inference(resolution,[],[f190,f174])).

fof(f174,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f190,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f188])).

fof(f4695,plain,
    ( ~ spl8_83
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | spl8_52
    | ~ spl8_56
    | ~ spl8_57
    | ~ spl8_58
    | ~ spl8_85
    | ~ spl8_138 ),
    inference(avatar_split_clause,[],[f4687,f2406,f1268,f680,f675,f670,f650,f229,f224,f219,f214,f1260])).

fof(f4687,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | spl8_52
    | ~ spl8_56
    | ~ spl8_57
    | ~ spl8_58
    | ~ spl8_85
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f231,f226,f221,f216,f672,f652,f682,f677,f2667,f1269,f175])).

fof(f175,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f1269,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl8_85 ),
    inference(avatar_component_clause,[],[f1268])).

fof(f652,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl8_52 ),
    inference(avatar_component_clause,[],[f650])).

fof(f4539,plain,
    ( spl8_47
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f4536,f357,f573])).

fof(f573,plain,
    ( spl8_47
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f357,plain,
    ( spl8_21
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f4536,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl8_21 ),
    inference(resolution,[],[f358,f110])).

fof(f110,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f358,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f357])).

fof(f4506,plain,
    ( spl8_21
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_23 ),
    inference(avatar_split_clause,[],[f1579,f368,f208,f203,f198,f357])).

fof(f203,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f208,plain,
    ( spl8_7
  <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f368,plain,
    ( spl8_23
  <=> v1_partfun1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f1579,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_23 ),
    inference(unit_resulting_resolution,[],[f200,f210,f205,f369,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f369,plain,
    ( ~ v1_partfun1(sK3,u1_struct_0(sK0))
    | spl8_23 ),
    inference(avatar_component_clause,[],[f368])).

fof(f205,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f203])).

fof(f210,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f208])).

fof(f4503,plain,
    ( spl8_86
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_30
    | spl8_44 ),
    inference(avatar_split_clause,[],[f4502,f547,f445,f198,f193,f188,f1282])).

fof(f1282,plain,
    ( spl8_86
  <=> v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f547,plain,
    ( spl8_44
  <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f4502,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_30
    | spl8_44 ),
    inference(forward_demodulation,[],[f2313,f447])).

fof(f2313,plain,
    ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_44 ),
    inference(unit_resulting_resolution,[],[f200,f195,f190,f548,f123])).

fof(f548,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl8_44 ),
    inference(avatar_component_clause,[],[f547])).

fof(f4298,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3)
    | k1_xboole_0 != sK3
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4294,plain,
    ( k1_xboole_0 != sK3
    | u1_struct_0(sK0) != k1_relat_1(sK3)
    | k2_relat_1(k1_xboole_0) != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4293,plain,
    ( spl8_199
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f4282,f547,f4284])).

fof(f4284,plain,
    ( spl8_199
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_199])])).

fof(f4282,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_44 ),
    inference(resolution,[],[f549,f110])).

fof(f549,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f547])).

fof(f4195,plain,
    ( spl8_30
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f4182,f361,f445])).

fof(f361,plain,
    ( spl8_22
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f4182,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f438,f119])).

fof(f119,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f438,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f363,f117])).

fof(f117,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f73,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f363,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f361])).

fof(f4079,plain,
    ( ~ spl8_52
    | spl8_1
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f638,f445,f178,f650])).

fof(f638,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl8_1
    | ~ spl8_30 ),
    inference(backward_demodulation,[],[f180,f447])).

fof(f180,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f178])).

fof(f4078,plain,
    ( spl8_53
    | ~ spl8_2
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f639,f445,f182,f655])).

fof(f655,plain,
    ( spl8_53
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f639,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_2
    | ~ spl8_30 ),
    inference(backward_demodulation,[],[f183,f447])).

fof(f183,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f182])).

fof(f4077,plain,
    ( spl8_56
    | ~ spl8_5
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f642,f445,f198,f670])).

fof(f642,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_30 ),
    inference(backward_demodulation,[],[f200,f447])).

fof(f4004,plain,
    ( ~ spl8_83
    | ~ spl8_53
    | spl8_85
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_40
    | ~ spl8_54
    | ~ spl8_55
    | ~ spl8_56
    | ~ spl8_138 ),
    inference(avatar_split_clause,[],[f4003,f2406,f670,f665,f660,f526,f298,f219,f214,f1268,f655,f1260])).

fof(f660,plain,
    ( spl8_54
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f665,plain,
    ( spl8_55
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f4003,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_40
    | ~ spl8_54
    | ~ spl8_55
    | ~ spl8_56
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f4002,f300])).

fof(f4002,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_40
    | ~ spl8_54
    | ~ spl8_55
    | ~ spl8_56
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f4001,f527])).

fof(f4001,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_54
    | ~ spl8_55
    | ~ spl8_56
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f4000,f221])).

fof(f4000,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl8_8
    | ~ spl8_54
    | ~ spl8_55
    | ~ spl8_56
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f3999,f216])).

fof(f3999,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl8_54
    | ~ spl8_55
    | ~ spl8_56
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f1273,f2667])).

fof(f1273,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl8_54
    | ~ spl8_55
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f1272,f672])).

fof(f1272,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl8_54
    | ~ spl8_55 ),
    inference(subsumption_resolution,[],[f1195,f667])).

fof(f667,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl8_55 ),
    inference(avatar_component_clause,[],[f665])).

fof(f1195,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl8_54 ),
    inference(resolution,[],[f662,f173])).

fof(f173,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f662,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f660])).

fof(f3543,plain,
    ( ~ spl8_44
    | spl8_22
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f3001,f493,f361,f547])).

fof(f493,plain,
    ( spl8_35
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f3001,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl8_35 ),
    inference(resolution,[],[f495,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f495,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f493])).

fof(f3541,plain,
    ( ~ spl8_44
    | spl8_22
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f2066,f188,f361,f547])).

fof(f2066,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl8_3 ),
    inference(resolution,[],[f190,f128])).

fof(f3532,plain,
    ( ~ spl8_37
    | spl8_39
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_36
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f3531,f512,f504,f267,f229,f224,f198,f193,f188,f182,f516,f508])).

fof(f508,plain,
    ( spl8_37
  <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f516,plain,
    ( spl8_39
  <=> v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f267,plain,
    ( spl8_13
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f504,plain,
    ( spl8_36
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f512,plain,
    ( spl8_38
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f3531,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_36
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3530,f231])).

fof(f3530,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_13
    | ~ spl8_36
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3529,f226])).

fof(f3529,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_13
    | ~ spl8_36
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3528,f269])).

fof(f269,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f267])).

fof(f3528,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_36
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3527,f505])).

fof(f505,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f504])).

fof(f3527,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3526,f513])).

fof(f513,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f512])).

fof(f3526,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f3525,f200])).

fof(f3525,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f498,f195])).

fof(f498,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f462,f183])).

fof(f462,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_3 ),
    inference(resolution,[],[f190,f175])).

fof(f3477,plain,
    ( ~ spl8_37
    | ~ spl8_1
    | spl8_39
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f3476,f512,f229,f224,f219,f214,f208,f203,f198,f516,f178,f508])).

fof(f3476,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3475,f231])).

fof(f3475,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3474,f226])).

fof(f3474,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3473,f221])).

fof(f3473,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3472,f216])).

fof(f3472,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3471,f210])).

fof(f3471,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3470,f205])).

fof(f3470,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3365,f200])).

fof(f3365,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_38 ),
    inference(resolution,[],[f513,f174])).

fof(f3469,plain,
    ( ~ spl8_37
    | ~ spl8_39
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_36
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f3468,f512,f504,f267,f229,f224,f198,f193,f188,f182,f516,f508])).

fof(f3468,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_36
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3467,f231])).

fof(f3467,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_13
    | ~ spl8_36
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3466,f226])).

fof(f3466,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_13
    | ~ spl8_36
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3465,f269])).

fof(f3465,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_36
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3464,f505])).

fof(f3464,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3463,f513])).

fof(f3463,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f3462,f200])).

fof(f3462,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1115,f195])).

fof(f1115,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_3 ),
    inference(resolution,[],[f190,f176])).

fof(f3409,plain,
    ( ~ spl8_37
    | ~ spl8_39
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f3408,f512,f229,f224,f219,f214,f208,f203,f198,f178,f516,f508])).

fof(f3408,plain,
    ( v5_pre_topc(sK3,sK0,sK1)
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3407,f231])).

fof(f3407,plain,
    ( v5_pre_topc(sK3,sK0,sK1)
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3406,f226])).

fof(f3406,plain,
    ( v5_pre_topc(sK3,sK0,sK1)
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3405,f221])).

fof(f3405,plain,
    ( v5_pre_topc(sK3,sK0,sK1)
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3404,f216])).

fof(f3404,plain,
    ( v5_pre_topc(sK3,sK0,sK1)
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3403,f210])).

fof(f3403,plain,
    ( v5_pre_topc(sK3,sK0,sK1)
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3402,f205])).

fof(f3402,plain,
    ( v5_pre_topc(sK3,sK0,sK1)
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_5
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f3366,f200])).

fof(f3366,plain,
    ( v5_pre_topc(sK3,sK0,sK1)
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_38 ),
    inference(resolution,[],[f513,f173])).

fof(f3353,plain,
    ( spl8_38
    | ~ spl8_3
    | ~ spl8_91 ),
    inference(avatar_split_clause,[],[f3330,f1347,f188,f512])).

fof(f1347,plain,
    ( spl8_91
  <=> r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f3330,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl8_3
    | ~ spl8_91 ),
    inference(resolution,[],[f1349,f469])).

fof(f469,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) )
    | ~ spl8_3 ),
    inference(resolution,[],[f190,f157])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f1349,plain,
    ( r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0))
    | ~ spl8_91 ),
    inference(avatar_component_clause,[],[f1347])).

fof(f3277,plain,
    ( spl8_141
    | ~ spl8_5
    | ~ spl8_17
    | ~ spl8_51 ),
    inference(avatar_split_clause,[],[f3254,f634,f333,f198,f2440])).

fof(f2440,plain,
    ( spl8_141
  <=> v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_141])])).

fof(f333,plain,
    ( spl8_17
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f634,plain,
    ( spl8_51
  <=> r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f3254,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1))
    | ~ spl8_5
    | ~ spl8_17
    | ~ spl8_51 ),
    inference(unit_resulting_resolution,[],[f335,f200,f636,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f636,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f634])).

fof(f335,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f333])).

fof(f3207,plain,
    ( spl8_169
    | ~ spl8_59
    | ~ spl8_138 ),
    inference(avatar_split_clause,[],[f3186,f2406,f685,f3107])).

fof(f3107,plain,
    ( spl8_169
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_169])])).

fof(f685,plain,
    ( spl8_59
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f3186,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_59
    | ~ spl8_138 ),
    inference(resolution,[],[f3083,f119])).

fof(f3083,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ spl8_59
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f2972,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f2972,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ spl8_59
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f687,f2940,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f2940,plain,
    ( ! [X0] : v4_relat_1(k1_xboole_0,X0)
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f2667,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f687,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_59 ),
    inference(avatar_component_clause,[],[f685])).

fof(f3173,plain,
    ( spl8_173
    | ~ spl8_59
    | ~ spl8_138 ),
    inference(avatar_split_clause,[],[f3144,f2406,f685,f3164])).

fof(f3164,plain,
    ( spl8_173
  <=> k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_173])])).

fof(f3144,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ spl8_59
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f2972,f2981,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2981,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | ~ spl8_59
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f687,f2941,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f2941,plain,
    ( ! [X0] : v5_relat_1(k1_xboole_0,X0)
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f2667,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f2860,plain,
    ( spl8_158
    | ~ spl8_59
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_split_clause,[],[f2859,f1282,f1223,f685,f2854])).

fof(f2854,plain,
    ( spl8_158
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_158])])).

fof(f1223,plain,
    ( spl8_78
  <=> v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f2859,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl8_59
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f2858,f687])).

fof(f2858,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f2848,f1225])).

fof(f1225,plain,
    ( v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl8_78 ),
    inference(avatar_component_clause,[],[f1223])).

fof(f2848,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl8_86 ),
    inference(resolution,[],[f1284,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f1284,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl8_86 ),
    inference(avatar_component_clause,[],[f1282])).

fof(f2740,plain,
    ( spl8_78
    | ~ spl8_54 ),
    inference(avatar_split_clause,[],[f2724,f660,f1223])).

fof(f2724,plain,
    ( v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl8_54 ),
    inference(resolution,[],[f662,f154])).

fof(f2689,plain,
    ( spl8_54
    | ~ spl8_138 ),
    inference(avatar_contradiction_clause,[],[f2668])).

fof(f2668,plain,
    ( $false
    | spl8_54
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f661,f2539,f142])).

fof(f661,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl8_54 ),
    inference(avatar_component_clause,[],[f660])).

fof(f2613,plain,
    ( spl8_59
    | ~ spl8_57 ),
    inference(avatar_split_clause,[],[f2600,f675,f685])).

fof(f2600,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_57 ),
    inference(resolution,[],[f677,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2553,plain,
    ( spl8_67
    | ~ spl8_138 ),
    inference(avatar_contradiction_clause,[],[f2540])).

fof(f2540,plain,
    ( $false
    | spl8_67
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f918,f2515,f139])).

fof(f918,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | spl8_67 ),
    inference(avatar_component_clause,[],[f917])).

fof(f917,plain,
    ( spl8_67
  <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f2533,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2532,plain,
    ( spl8_147
    | ~ spl8_17
    | ~ spl8_34
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f2531,f551,f488,f333,f2526])).

fof(f2526,plain,
    ( spl8_147
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).

fof(f488,plain,
    ( spl8_34
  <=> v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f551,plain,
    ( spl8_45
  <=> v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f2531,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | ~ spl8_17
    | ~ spl8_34
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f2530,f335])).

fof(f2530,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_34
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f2524,f490])).

fof(f490,plain,
    ( v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f488])).

fof(f2524,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_relat_1(sK3)
    | ~ spl8_45 ),
    inference(resolution,[],[f553,f133])).

fof(f553,plain,
    ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f551])).

fof(f2457,plain,(
    spl8_138 ),
    inference(avatar_contradiction_clause,[],[f2456])).

fof(f2456,plain,
    ( $false
    | spl8_138 ),
    inference(subsumption_resolution,[],[f2448,f170])).

fof(f170,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f82])).

fof(f2448,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl8_138 ),
    inference(resolution,[],[f2408,f142])).

fof(f2408,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl8_138 ),
    inference(avatar_component_clause,[],[f2406])).

fof(f2324,plain,
    ( spl8_45
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_44 ),
    inference(avatar_split_clause,[],[f2313,f547,f198,f193,f188,f551])).

fof(f2200,plain,
    ( ~ spl8_14
    | spl8_40 ),
    inference(avatar_split_clause,[],[f2198,f526,f283])).

fof(f283,plain,
    ( spl8_14
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f2198,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl8_40 ),
    inference(unit_resulting_resolution,[],[f528,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f528,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl8_40 ),
    inference(avatar_component_clause,[],[f526])).

fof(f2089,plain,
    ( spl8_34
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f2063,f188,f488])).

fof(f2063,plain,
    ( v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl8_3 ),
    inference(resolution,[],[f190,f154])).

fof(f2075,plain,
    ( spl8_35
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f2047,f188,f493])).

fof(f2047,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f170,f190,f157])).

fof(f1963,plain,
    ( ~ spl8_67
    | spl8_57 ),
    inference(avatar_split_clause,[],[f1956,f675,f917])).

fof(f1956,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | spl8_57 ),
    inference(resolution,[],[f676,f142])).

fof(f676,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl8_57 ),
    inference(avatar_component_clause,[],[f675])).

fof(f1953,plain,
    ( spl8_51
    | ~ spl8_17
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f1951,f338,f333,f634])).

fof(f338,plain,
    ( spl8_18
  <=> v5_relat_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f1951,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))
    | ~ spl8_17
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f335,f340,f124])).

fof(f340,plain,
    ( v5_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f338])).

fof(f1948,plain,
    ( spl8_18
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f1938,f203,f338])).

fof(f1938,plain,
    ( v5_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl8_6 ),
    inference(resolution,[],[f205,f155])).

fof(f1752,plain,
    ( ~ spl8_12
    | spl8_36 ),
    inference(avatar_split_clause,[],[f1750,f504,f252])).

fof(f252,plain,
    ( spl8_12
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f1750,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl8_36 ),
    inference(unit_resulting_resolution,[],[f506,f129])).

fof(f506,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl8_36 ),
    inference(avatar_component_clause,[],[f504])).

fof(f1695,plain,
    ( spl8_94
    | ~ spl8_17
    | ~ spl8_19
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f1694,f368,f343,f333,f1375])).

fof(f1375,plain,
    ( spl8_94
  <=> u1_struct_0(sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f343,plain,
    ( spl8_19
  <=> v4_relat_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f1694,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | ~ spl8_17
    | ~ spl8_19
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f1693,f335])).

fof(f1693,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_19
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f1691,f345])).

fof(f345,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK0))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f343])).

fof(f1691,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,u1_struct_0(sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl8_23 ),
    inference(resolution,[],[f370,f133])).

fof(f370,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK0))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f368])).

fof(f1641,plain,
    ( ~ spl8_21
    | ~ spl8_6
    | spl8_22 ),
    inference(avatar_split_clause,[],[f1632,f361,f203,f357])).

fof(f1632,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl8_6
    | spl8_22 ),
    inference(unit_resulting_resolution,[],[f205,f362,f128])).

fof(f362,plain,
    ( ~ v1_xboole_0(sK3)
    | spl8_22 ),
    inference(avatar_component_clause,[],[f361])).

fof(f1350,plain,
    ( spl8_91
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1343,f343,f333,f1347])).

fof(f1343,plain,
    ( r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0))
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f335,f345,f126])).

fof(f886,plain,
    ( spl8_19
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f874,f203,f343])).

fof(f874,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK0))
    | ~ spl8_6 ),
    inference(resolution,[],[f205,f154])).

fof(f775,plain,
    ( spl8_55
    | ~ spl8_4
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f641,f445,f193,f665])).

fof(f641,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl8_4
    | ~ spl8_30 ),
    inference(backward_demodulation,[],[f195,f447])).

fof(f772,plain,
    ( spl8_58
    | ~ spl8_7
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f644,f445,f208,f680])).

fof(f644,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_7
    | ~ spl8_30 ),
    inference(backward_demodulation,[],[f210,f447])).

fof(f726,plain,
    ( spl8_27
    | ~ spl8_5
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f711,f333,f198,f404])).

fof(f404,plain,
    ( spl8_27
  <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f711,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ spl8_5
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f200,f170,f335,f131])).

fof(f355,plain,
    ( spl8_17
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f322,f203,f333])).

fof(f322,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f205,f153])).

fof(f301,plain,
    ( spl8_15
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f287,f229,f224,f298])).

fof(f287,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f226,f231,f112])).

fof(f112,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f286,plain,
    ( spl8_14
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f271,f224,f283])).

fof(f271,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f226,f111])).

fof(f111,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f270,plain,
    ( spl8_13
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f256,f219,f214,f267])).

fof(f256,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f216,f221,f112])).

fof(f255,plain,
    ( spl8_12
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f240,f214,f252])).

fof(f240,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f216,f111])).

fof(f232,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f92,f229])).

fof(f92,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f64,f68,f67,f66,f65])).

fof(f65,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f227,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f93,f224])).

fof(f93,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f222,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f94,f219])).

fof(f94,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

fof(f217,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f95,f214])).

fof(f95,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

fof(f212,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f162,f198])).

fof(f162,plain,(
    v1_funct_1(sK3) ),
    inference(definition_unfolding,[],[f96,f102])).

fof(f102,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f69])).

fof(f96,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f211,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f161,f208])).

fof(f161,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f97,f102])).

fof(f97,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f69])).

fof(f206,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f160,f203])).

fof(f160,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f98,f102])).

fof(f98,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f69])).

fof(f196,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f100,f193])).

fof(f100,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f69])).

fof(f191,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f101,f188])).

fof(f101,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f69])).

fof(f186,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f159,f182,f178])).

fof(f159,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,sK1) ),
    inference(definition_unfolding,[],[f103,f102])).

fof(f103,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

fof(f185,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f158,f182,f178])).

fof(f158,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1) ),
    inference(definition_unfolding,[],[f104,f102])).

fof(f104,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (25189)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (25200)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (25183)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (25186)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (25184)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (25182)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (25204)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (25196)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (25199)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (25208)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (25188)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (25193)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (25187)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (25185)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (25207)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (25203)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (25197)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (25206)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (25210)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (25209)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (25195)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (25199)Refutation not found, incomplete strategy% (25199)------------------------------
% 0.21/0.55  % (25199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25199)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (25199)Memory used [KB]: 10746
% 0.21/0.55  % (25199)Time elapsed: 0.125 s
% 0.21/0.55  % (25199)------------------------------
% 0.21/0.55  % (25199)------------------------------
% 0.21/0.55  % (25198)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (25202)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (25201)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (25190)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (25211)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (25193)Refutation not found, incomplete strategy% (25193)------------------------------
% 0.21/0.56  % (25193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (25193)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (25193)Memory used [KB]: 10874
% 0.21/0.56  % (25193)Time elapsed: 0.147 s
% 0.21/0.56  % (25193)------------------------------
% 0.21/0.56  % (25193)------------------------------
% 0.21/0.56  % (25191)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (25204)Refutation not found, incomplete strategy% (25204)------------------------------
% 0.21/0.56  % (25204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (25204)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (25204)Memory used [KB]: 11129
% 0.21/0.56  % (25204)Time elapsed: 0.088 s
% 0.21/0.56  % (25204)------------------------------
% 0.21/0.56  % (25204)------------------------------
% 0.21/0.56  % (25194)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (25192)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (25205)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (25203)Refutation not found, incomplete strategy% (25203)------------------------------
% 0.21/0.56  % (25203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (25203)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (25203)Memory used [KB]: 1791
% 0.21/0.56  % (25203)Time elapsed: 0.149 s
% 0.21/0.56  % (25203)------------------------------
% 0.21/0.56  % (25203)------------------------------
% 0.21/0.56  % (25192)Refutation not found, incomplete strategy% (25192)------------------------------
% 0.21/0.56  % (25192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (25192)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (25192)Memory used [KB]: 10874
% 0.21/0.56  % (25192)Time elapsed: 0.151 s
% 0.21/0.56  % (25192)------------------------------
% 0.21/0.56  % (25192)------------------------------
% 0.21/0.57  % (25182)Refutation not found, incomplete strategy% (25182)------------------------------
% 0.21/0.57  % (25182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (25182)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (25182)Memory used [KB]: 1791
% 0.21/0.57  % (25182)Time elapsed: 0.154 s
% 0.21/0.57  % (25182)------------------------------
% 0.21/0.57  % (25182)------------------------------
% 0.21/0.58  % (25191)Refutation not found, incomplete strategy% (25191)------------------------------
% 0.21/0.58  % (25191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (25191)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (25191)Memory used [KB]: 10874
% 0.21/0.58  % (25191)Time elapsed: 0.155 s
% 0.21/0.58  % (25191)------------------------------
% 0.21/0.58  % (25191)------------------------------
% 2.10/0.70  % (25215)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.10/0.70  % (25214)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.10/0.70  % (25213)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.69/0.71  % (25212)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.69/0.72  % (25216)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.69/0.74  % (25218)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.69/0.74  % (25217)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 3.16/0.78  % (25207)Refutation found. Thanks to Tanya!
% 3.16/0.78  % SZS status Theorem for theBenchmark
% 3.16/0.78  % SZS output start Proof for theBenchmark
% 3.16/0.78  % (25212)Refutation not found, incomplete strategy% (25212)------------------------------
% 3.16/0.78  % (25212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.78  % (25212)Termination reason: Refutation not found, incomplete strategy
% 3.16/0.78  
% 3.16/0.78  % (25212)Memory used [KB]: 6652
% 3.16/0.78  % (25212)Time elapsed: 0.155 s
% 3.16/0.78  % (25212)------------------------------
% 3.16/0.78  % (25212)------------------------------
% 3.16/0.78  fof(f4957,plain,(
% 3.16/0.78    $false),
% 3.16/0.78    inference(avatar_sat_refutation,[],[f185,f186,f191,f196,f206,f211,f212,f217,f222,f227,f232,f255,f270,f286,f301,f355,f726,f772,f775,f886,f1350,f1641,f1695,f1752,f1948,f1953,f1963,f2075,f2089,f2200,f2324,f2457,f2532,f2533,f2553,f2613,f2689,f2740,f2860,f3173,f3207,f3277,f3353,f3409,f3469,f3477,f3532,f3541,f3543,f4004,f4077,f4078,f4079,f4195,f4293,f4294,f4298,f4503,f4506,f4539,f4695,f4837,f4918,f4953,f4955,f4956])).
% 3.16/0.78  fof(f4956,plain,(
% 3.16/0.78    k1_xboole_0 != sK3 | k1_xboole_0 != u1_struct_0(sK1) | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.16/0.78    introduced(theory_tautology_sat_conflict,[])).
% 3.16/0.78  fof(f4955,plain,(
% 3.16/0.78    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0) | k1_xboole_0 != sK3 | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1))),
% 3.16/0.78    introduced(theory_tautology_sat_conflict,[])).
% 3.16/0.78  fof(f4953,plain,(
% 3.16/0.78    ~spl8_83 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_52 | ~spl8_56 | ~spl8_57 | ~spl8_58 | spl8_85 | ~spl8_138),
% 3.16/0.78    inference(avatar_split_clause,[],[f4945,f2406,f1268,f680,f675,f670,f650,f229,f224,f219,f214,f1260])).
% 3.16/0.78  fof(f1260,plain,(
% 3.16/0.78    spl8_83 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).
% 3.16/0.78  fof(f214,plain,(
% 3.16/0.78    spl8_8 <=> l1_pre_topc(sK1)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 3.16/0.78  fof(f219,plain,(
% 3.16/0.78    spl8_9 <=> v2_pre_topc(sK1)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 3.16/0.78  fof(f224,plain,(
% 3.16/0.78    spl8_10 <=> l1_pre_topc(sK0)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 3.16/0.78  fof(f229,plain,(
% 3.16/0.78    spl8_11 <=> v2_pre_topc(sK0)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 3.16/0.78  fof(f650,plain,(
% 3.16/0.78    spl8_52 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 3.16/0.78  fof(f670,plain,(
% 3.16/0.78    spl8_56 <=> v1_funct_1(k1_xboole_0)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).
% 3.16/0.78  fof(f675,plain,(
% 3.16/0.78    spl8_57 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 3.16/0.78  fof(f680,plain,(
% 3.16/0.78    spl8_58 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).
% 3.16/0.78  fof(f1268,plain,(
% 3.16/0.78    spl8_85 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).
% 3.16/0.78  fof(f2406,plain,(
% 3.16/0.78    spl8_138 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).
% 3.16/0.78  fof(f4945,plain,(
% 3.16/0.78    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_52 | ~spl8_56 | ~spl8_57 | ~spl8_58 | spl8_85 | ~spl8_138)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f231,f226,f221,f216,f672,f651,f682,f677,f2667,f1270,f176])).
% 3.16/0.78  fof(f176,plain,(
% 3.16/0.78    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(duplicate_literal_removal,[],[f167])).
% 3.16/0.78  fof(f167,plain,(
% 3.16/0.78    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(equality_resolution,[],[f115])).
% 3.16/0.78  fof(f115,plain,(
% 3.16/0.78    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f71])).
% 3.16/0.78  fof(f71,plain,(
% 3.16/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.16/0.78    inference(nnf_transformation,[],[f44])).
% 3.16/0.78  fof(f44,plain,(
% 3.16/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.16/0.78    inference(flattening,[],[f43])).
% 3.16/0.78  fof(f43,plain,(
% 3.16/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.16/0.78    inference(ennf_transformation,[],[f29])).
% 3.16/0.78  fof(f29,axiom,(
% 3.16/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 3.16/0.78  fof(f1270,plain,(
% 3.16/0.78    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl8_85),
% 3.16/0.78    inference(avatar_component_clause,[],[f1268])).
% 3.16/0.78  fof(f2667,plain,(
% 3.16/0.78    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl8_138),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f2539,f142])).
% 3.16/0.78  fof(f142,plain,(
% 3.16/0.78    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f87])).
% 3.16/0.78  fof(f87,plain,(
% 3.16/0.78    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.16/0.78    inference(nnf_transformation,[],[f11])).
% 3.16/0.78  fof(f11,axiom,(
% 3.16/0.78    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.16/0.78  fof(f2539,plain,(
% 3.16/0.78    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl8_138),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f2515,f139])).
% 3.16/0.78  fof(f139,plain,(
% 3.16/0.78    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f86])).
% 3.16/0.78  fof(f86,plain,(
% 3.16/0.78    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.16/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f84,f85])).
% 3.16/0.78  fof(f85,plain,(
% 3.16/0.78    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 3.16/0.78    introduced(choice_axiom,[])).
% 3.16/0.78  fof(f84,plain,(
% 3.16/0.78    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.16/0.78    inference(rectify,[],[f83])).
% 3.16/0.78  fof(f83,plain,(
% 3.16/0.78    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.16/0.78    inference(nnf_transformation,[],[f56])).
% 3.16/0.78  fof(f56,plain,(
% 3.16/0.78    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.16/0.78    inference(ennf_transformation,[],[f2])).
% 3.16/0.78  fof(f2,axiom,(
% 3.16/0.78    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.16/0.78  fof(f2515,plain,(
% 3.16/0.78    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_138),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f105,f2407,f156])).
% 3.16/0.78  fof(f156,plain,(
% 3.16/0.78    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f60])).
% 3.16/0.78  fof(f60,plain,(
% 3.16/0.78    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.16/0.78    inference(ennf_transformation,[],[f12])).
% 3.16/0.78  fof(f12,axiom,(
% 3.16/0.78    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 3.16/0.78  fof(f2407,plain,(
% 3.16/0.78    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl8_138),
% 3.16/0.78    inference(avatar_component_clause,[],[f2406])).
% 3.16/0.78  fof(f105,plain,(
% 3.16/0.78    v1_xboole_0(k1_xboole_0)),
% 3.16/0.78    inference(cnf_transformation,[],[f3])).
% 3.16/0.78  fof(f3,axiom,(
% 3.16/0.78    v1_xboole_0(k1_xboole_0)),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.16/0.78  fof(f677,plain,(
% 3.16/0.78    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl8_57),
% 3.16/0.78    inference(avatar_component_clause,[],[f675])).
% 3.16/0.78  fof(f682,plain,(
% 3.16/0.78    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl8_58),
% 3.16/0.78    inference(avatar_component_clause,[],[f680])).
% 3.16/0.78  fof(f651,plain,(
% 3.16/0.78    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~spl8_52),
% 3.16/0.78    inference(avatar_component_clause,[],[f650])).
% 3.16/0.78  fof(f672,plain,(
% 3.16/0.78    v1_funct_1(k1_xboole_0) | ~spl8_56),
% 3.16/0.78    inference(avatar_component_clause,[],[f670])).
% 3.16/0.78  fof(f216,plain,(
% 3.16/0.78    l1_pre_topc(sK1) | ~spl8_8),
% 3.16/0.78    inference(avatar_component_clause,[],[f214])).
% 3.16/0.78  fof(f221,plain,(
% 3.16/0.78    v2_pre_topc(sK1) | ~spl8_9),
% 3.16/0.78    inference(avatar_component_clause,[],[f219])).
% 3.16/0.78  fof(f226,plain,(
% 3.16/0.78    l1_pre_topc(sK0) | ~spl8_10),
% 3.16/0.78    inference(avatar_component_clause,[],[f224])).
% 3.16/0.78  fof(f231,plain,(
% 3.16/0.78    v2_pre_topc(sK0) | ~spl8_11),
% 3.16/0.78    inference(avatar_component_clause,[],[f229])).
% 3.16/0.78  fof(f4918,plain,(
% 3.16/0.78    spl8_52 | ~spl8_1 | ~spl8_30),
% 3.16/0.78    inference(avatar_split_clause,[],[f4917,f445,f178,f650])).
% 3.16/0.78  fof(f178,plain,(
% 3.16/0.78    spl8_1 <=> v5_pre_topc(sK3,sK0,sK1)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 3.16/0.78  fof(f445,plain,(
% 3.16/0.78    spl8_30 <=> k1_xboole_0 = sK3),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 3.16/0.78  fof(f4917,plain,(
% 3.16/0.78    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl8_1 | ~spl8_30)),
% 3.16/0.78    inference(forward_demodulation,[],[f179,f447])).
% 3.16/0.78  fof(f447,plain,(
% 3.16/0.78    k1_xboole_0 = sK3 | ~spl8_30),
% 3.16/0.78    inference(avatar_component_clause,[],[f445])).
% 3.16/0.78  fof(f179,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,sK1) | ~spl8_1),
% 3.16/0.78    inference(avatar_component_clause,[],[f178])).
% 3.16/0.78  fof(f4837,plain,(
% 3.16/0.78    ~spl8_85 | ~spl8_83 | spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8 | ~spl8_9 | ~spl8_15 | ~spl8_30 | ~spl8_40 | ~spl8_138),
% 3.16/0.78    inference(avatar_split_clause,[],[f4836,f2406,f526,f445,f298,f219,f214,f198,f193,f188,f182,f1260,f1268])).
% 3.16/0.78  fof(f182,plain,(
% 3.16/0.78    spl8_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 3.16/0.78  fof(f188,plain,(
% 3.16/0.78    spl8_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 3.16/0.78  fof(f193,plain,(
% 3.16/0.78    spl8_4 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 3.16/0.78  fof(f198,plain,(
% 3.16/0.78    spl8_5 <=> v1_funct_1(sK3)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 3.16/0.78  fof(f298,plain,(
% 3.16/0.78    spl8_15 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 3.16/0.78  fof(f526,plain,(
% 3.16/0.78    spl8_40 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 3.16/0.78  fof(f4836,plain,(
% 3.16/0.78    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8 | ~spl8_9 | ~spl8_15 | ~spl8_30 | ~spl8_40 | ~spl8_138)),
% 3.16/0.78    inference(forward_demodulation,[],[f4835,f447])).
% 3.16/0.78  fof(f4835,plain,(
% 3.16/0.78    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8 | ~spl8_9 | ~spl8_15 | ~spl8_30 | ~spl8_40 | ~spl8_138)),
% 3.16/0.78    inference(subsumption_resolution,[],[f4834,f2667])).
% 3.16/0.78  fof(f4834,plain,(
% 3.16/0.78    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8 | ~spl8_9 | ~spl8_15 | ~spl8_30 | ~spl8_40)),
% 3.16/0.78    inference(forward_demodulation,[],[f4833,f447])).
% 3.16/0.78  fof(f4833,plain,(
% 3.16/0.78    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8 | ~spl8_9 | ~spl8_15 | ~spl8_30 | ~spl8_40)),
% 3.16/0.78    inference(forward_demodulation,[],[f4832,f447])).
% 3.16/0.78  fof(f4832,plain,(
% 3.16/0.78    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8 | ~spl8_9 | ~spl8_15 | ~spl8_40)),
% 3.16/0.78    inference(subsumption_resolution,[],[f4831,f300])).
% 3.16/0.78  fof(f300,plain,(
% 3.16/0.78    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl8_15),
% 3.16/0.78    inference(avatar_component_clause,[],[f298])).
% 3.16/0.78  fof(f4831,plain,(
% 3.16/0.78    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8 | ~spl8_9 | ~spl8_40)),
% 3.16/0.78    inference(subsumption_resolution,[],[f4830,f527])).
% 3.16/0.78  fof(f527,plain,(
% 3.16/0.78    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl8_40),
% 3.16/0.78    inference(avatar_component_clause,[],[f526])).
% 3.16/0.78  fof(f4830,plain,(
% 3.16/0.78    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8 | ~spl8_9)),
% 3.16/0.78    inference(subsumption_resolution,[],[f4829,f221])).
% 3.16/0.78  fof(f4829,plain,(
% 3.16/0.78    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8)),
% 3.16/0.78    inference(subsumption_resolution,[],[f1145,f216])).
% 3.16/0.78  fof(f1145,plain,(
% 3.16/0.78    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5)),
% 3.16/0.78    inference(subsumption_resolution,[],[f1144,f200])).
% 3.16/0.78  fof(f200,plain,(
% 3.16/0.78    v1_funct_1(sK3) | ~spl8_5),
% 3.16/0.78    inference(avatar_component_clause,[],[f198])).
% 3.16/0.78  fof(f1144,plain,(
% 3.16/0.78    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl8_2 | ~spl8_3 | ~spl8_4)),
% 3.16/0.78    inference(subsumption_resolution,[],[f1143,f195])).
% 3.16/0.78  fof(f195,plain,(
% 3.16/0.78    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl8_4),
% 3.16/0.78    inference(avatar_component_clause,[],[f193])).
% 3.16/0.78  fof(f1143,plain,(
% 3.16/0.78    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl8_2 | ~spl8_3)),
% 3.16/0.78    inference(subsumption_resolution,[],[f1117,f184])).
% 3.16/0.78  fof(f184,plain,(
% 3.16/0.78    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl8_2),
% 3.16/0.78    inference(avatar_component_clause,[],[f182])).
% 3.16/0.78  fof(f1117,plain,(
% 3.16/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl8_3),
% 3.16/0.78    inference(resolution,[],[f190,f174])).
% 3.16/0.78  fof(f174,plain,(
% 3.16/0.78    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(duplicate_literal_removal,[],[f165])).
% 3.16/0.78  fof(f165,plain,(
% 3.16/0.78    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(equality_resolution,[],[f113])).
% 3.16/0.78  fof(f113,plain,(
% 3.16/0.78    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f70])).
% 3.16/0.78  fof(f70,plain,(
% 3.16/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.16/0.78    inference(nnf_transformation,[],[f42])).
% 3.16/0.78  fof(f42,plain,(
% 3.16/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.16/0.78    inference(flattening,[],[f41])).
% 3.16/0.78  fof(f41,plain,(
% 3.16/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.16/0.78    inference(ennf_transformation,[],[f30])).
% 3.16/0.78  fof(f30,axiom,(
% 3.16/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).
% 3.16/0.78  fof(f190,plain,(
% 3.16/0.78    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl8_3),
% 3.16/0.78    inference(avatar_component_clause,[],[f188])).
% 3.16/0.78  fof(f4695,plain,(
% 3.16/0.78    ~spl8_83 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | spl8_52 | ~spl8_56 | ~spl8_57 | ~spl8_58 | ~spl8_85 | ~spl8_138),
% 3.16/0.78    inference(avatar_split_clause,[],[f4687,f2406,f1268,f680,f675,f670,f650,f229,f224,f219,f214,f1260])).
% 3.16/0.78  fof(f4687,plain,(
% 3.16/0.78    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | spl8_52 | ~spl8_56 | ~spl8_57 | ~spl8_58 | ~spl8_85 | ~spl8_138)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f231,f226,f221,f216,f672,f652,f682,f677,f2667,f1269,f175])).
% 3.16/0.78  fof(f175,plain,(
% 3.16/0.78    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(duplicate_literal_removal,[],[f166])).
% 3.16/0.78  fof(f166,plain,(
% 3.16/0.78    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(equality_resolution,[],[f116])).
% 3.16/0.78  fof(f116,plain,(
% 3.16/0.78    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f71])).
% 3.16/0.78  fof(f1269,plain,(
% 3.16/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl8_85),
% 3.16/0.78    inference(avatar_component_clause,[],[f1268])).
% 3.16/0.78  fof(f652,plain,(
% 3.16/0.78    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl8_52),
% 3.16/0.78    inference(avatar_component_clause,[],[f650])).
% 3.16/0.78  fof(f4539,plain,(
% 3.16/0.78    spl8_47 | ~spl8_21),
% 3.16/0.78    inference(avatar_split_clause,[],[f4536,f357,f573])).
% 3.16/0.78  fof(f573,plain,(
% 3.16/0.78    spl8_47 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 3.16/0.78  fof(f357,plain,(
% 3.16/0.78    spl8_21 <=> v1_xboole_0(u1_struct_0(sK1))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 3.16/0.78  fof(f4536,plain,(
% 3.16/0.78    k1_xboole_0 = u1_struct_0(sK1) | ~spl8_21),
% 3.16/0.78    inference(resolution,[],[f358,f110])).
% 3.16/0.78  fof(f110,plain,(
% 3.16/0.78    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f37])).
% 3.16/0.78  fof(f37,plain,(
% 3.16/0.78    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.16/0.78    inference(ennf_transformation,[],[f4])).
% 3.16/0.78  fof(f4,axiom,(
% 3.16/0.78    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 3.16/0.78  fof(f358,plain,(
% 3.16/0.78    v1_xboole_0(u1_struct_0(sK1)) | ~spl8_21),
% 3.16/0.78    inference(avatar_component_clause,[],[f357])).
% 3.16/0.78  fof(f4506,plain,(
% 3.16/0.78    spl8_21 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_23),
% 3.16/0.78    inference(avatar_split_clause,[],[f1579,f368,f208,f203,f198,f357])).
% 3.16/0.78  fof(f203,plain,(
% 3.16/0.78    spl8_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 3.16/0.78  fof(f208,plain,(
% 3.16/0.78    spl8_7 <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 3.16/0.78  fof(f368,plain,(
% 3.16/0.78    spl8_23 <=> v1_partfun1(sK3,u1_struct_0(sK0))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 3.16/0.78  fof(f1579,plain,(
% 3.16/0.78    v1_xboole_0(u1_struct_0(sK1)) | (~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_23)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f200,f210,f205,f369,f123])).
% 3.16/0.78  fof(f123,plain,(
% 3.16/0.78    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f47])).
% 3.16/0.78  fof(f47,plain,(
% 3.16/0.78    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.16/0.78    inference(flattening,[],[f46])).
% 3.16/0.78  fof(f46,plain,(
% 3.16/0.78    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.16/0.78    inference(ennf_transformation,[],[f22])).
% 3.16/0.78  fof(f22,axiom,(
% 3.16/0.78    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 3.16/0.78  fof(f369,plain,(
% 3.16/0.78    ~v1_partfun1(sK3,u1_struct_0(sK0)) | spl8_23),
% 3.16/0.78    inference(avatar_component_clause,[],[f368])).
% 3.16/0.78  fof(f205,plain,(
% 3.16/0.78    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl8_6),
% 3.16/0.78    inference(avatar_component_clause,[],[f203])).
% 3.16/0.78  fof(f210,plain,(
% 3.16/0.78    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl8_7),
% 3.16/0.78    inference(avatar_component_clause,[],[f208])).
% 3.16/0.78  fof(f4503,plain,(
% 3.16/0.78    spl8_86 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_30 | spl8_44),
% 3.16/0.78    inference(avatar_split_clause,[],[f4502,f547,f445,f198,f193,f188,f1282])).
% 3.16/0.78  fof(f1282,plain,(
% 3.16/0.78    spl8_86 <=> v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).
% 3.16/0.78  fof(f547,plain,(
% 3.16/0.78    spl8_44 <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 3.16/0.78  fof(f4502,plain,(
% 3.16/0.78    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_30 | spl8_44)),
% 3.16/0.78    inference(forward_demodulation,[],[f2313,f447])).
% 3.16/0.78  fof(f2313,plain,(
% 3.16/0.78    v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_44)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f200,f195,f190,f548,f123])).
% 3.16/0.78  fof(f548,plain,(
% 3.16/0.78    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl8_44),
% 3.16/0.78    inference(avatar_component_clause,[],[f547])).
% 3.16/0.78  fof(f4298,plain,(
% 3.16/0.78    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3) | k1_xboole_0 != sK3 | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1))),
% 3.16/0.78    introduced(theory_tautology_sat_conflict,[])).
% 3.16/0.78  fof(f4294,plain,(
% 3.16/0.78    k1_xboole_0 != sK3 | u1_struct_0(sK0) != k1_relat_1(sK3) | k2_relat_1(k1_xboole_0) != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 3.16/0.78    introduced(theory_tautology_sat_conflict,[])).
% 3.16/0.78  fof(f4293,plain,(
% 3.16/0.78    spl8_199 | ~spl8_44),
% 3.16/0.78    inference(avatar_split_clause,[],[f4282,f547,f4284])).
% 3.16/0.78  fof(f4284,plain,(
% 3.16/0.78    spl8_199 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_199])])).
% 3.16/0.78  fof(f4282,plain,(
% 3.16/0.78    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_44),
% 3.16/0.78    inference(resolution,[],[f549,f110])).
% 3.16/0.78  fof(f549,plain,(
% 3.16/0.78    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl8_44),
% 3.16/0.78    inference(avatar_component_clause,[],[f547])).
% 3.16/0.78  fof(f4195,plain,(
% 3.16/0.78    spl8_30 | ~spl8_22),
% 3.16/0.78    inference(avatar_split_clause,[],[f4182,f361,f445])).
% 3.16/0.78  fof(f361,plain,(
% 3.16/0.78    spl8_22 <=> v1_xboole_0(sK3)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 3.16/0.78  fof(f4182,plain,(
% 3.16/0.78    k1_xboole_0 = sK3 | ~spl8_22),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f438,f119])).
% 3.16/0.78  fof(f119,plain,(
% 3.16/0.78    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 3.16/0.78    inference(cnf_transformation,[],[f77])).
% 3.16/0.78  fof(f77,plain,(
% 3.16/0.78    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 3.16/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f76])).
% 3.16/0.78  fof(f76,plain,(
% 3.16/0.78    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 3.16/0.78    introduced(choice_axiom,[])).
% 3.16/0.78  fof(f45,plain,(
% 3.16/0.78    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.16/0.78    inference(ennf_transformation,[],[f5])).
% 3.16/0.78  fof(f5,axiom,(
% 3.16/0.78    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 3.16/0.78  fof(f438,plain,(
% 3.16/0.78    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl8_22),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f363,f117])).
% 3.16/0.78  fof(f117,plain,(
% 3.16/0.78    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f75])).
% 3.16/0.78  fof(f75,plain,(
% 3.16/0.78    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.16/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f73,f74])).
% 3.16/0.78  fof(f74,plain,(
% 3.16/0.78    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 3.16/0.78    introduced(choice_axiom,[])).
% 3.16/0.78  fof(f73,plain,(
% 3.16/0.78    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.16/0.78    inference(rectify,[],[f72])).
% 3.16/0.78  fof(f72,plain,(
% 3.16/0.78    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.16/0.78    inference(nnf_transformation,[],[f1])).
% 3.16/0.78  fof(f1,axiom,(
% 3.16/0.78    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 3.16/0.78  fof(f363,plain,(
% 3.16/0.78    v1_xboole_0(sK3) | ~spl8_22),
% 3.16/0.78    inference(avatar_component_clause,[],[f361])).
% 3.16/0.78  fof(f4079,plain,(
% 3.16/0.78    ~spl8_52 | spl8_1 | ~spl8_30),
% 3.16/0.78    inference(avatar_split_clause,[],[f638,f445,f178,f650])).
% 3.16/0.78  fof(f638,plain,(
% 3.16/0.78    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl8_1 | ~spl8_30)),
% 3.16/0.78    inference(backward_demodulation,[],[f180,f447])).
% 3.16/0.78  fof(f180,plain,(
% 3.16/0.78    ~v5_pre_topc(sK3,sK0,sK1) | spl8_1),
% 3.16/0.78    inference(avatar_component_clause,[],[f178])).
% 3.16/0.78  fof(f4078,plain,(
% 3.16/0.78    spl8_53 | ~spl8_2 | ~spl8_30),
% 3.16/0.78    inference(avatar_split_clause,[],[f639,f445,f182,f655])).
% 3.16/0.78  fof(f655,plain,(
% 3.16/0.78    spl8_53 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 3.16/0.78  fof(f639,plain,(
% 3.16/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl8_2 | ~spl8_30)),
% 3.16/0.78    inference(backward_demodulation,[],[f183,f447])).
% 3.16/0.78  fof(f183,plain,(
% 3.16/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_2),
% 3.16/0.78    inference(avatar_component_clause,[],[f182])).
% 3.16/0.78  fof(f4077,plain,(
% 3.16/0.78    spl8_56 | ~spl8_5 | ~spl8_30),
% 3.16/0.78    inference(avatar_split_clause,[],[f642,f445,f198,f670])).
% 3.16/0.78  fof(f642,plain,(
% 3.16/0.78    v1_funct_1(k1_xboole_0) | (~spl8_5 | ~spl8_30)),
% 3.16/0.78    inference(backward_demodulation,[],[f200,f447])).
% 3.16/0.78  fof(f4004,plain,(
% 3.16/0.78    ~spl8_83 | ~spl8_53 | spl8_85 | ~spl8_8 | ~spl8_9 | ~spl8_15 | ~spl8_40 | ~spl8_54 | ~spl8_55 | ~spl8_56 | ~spl8_138),
% 3.16/0.78    inference(avatar_split_clause,[],[f4003,f2406,f670,f665,f660,f526,f298,f219,f214,f1268,f655,f1260])).
% 3.16/0.78  fof(f660,plain,(
% 3.16/0.78    spl8_54 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).
% 3.16/0.78  fof(f665,plain,(
% 3.16/0.78    spl8_55 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).
% 3.16/0.78  fof(f4003,plain,(
% 3.16/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl8_8 | ~spl8_9 | ~spl8_15 | ~spl8_40 | ~spl8_54 | ~spl8_55 | ~spl8_56 | ~spl8_138)),
% 3.16/0.78    inference(subsumption_resolution,[],[f4002,f300])).
% 3.16/0.78  fof(f4002,plain,(
% 3.16/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl8_8 | ~spl8_9 | ~spl8_40 | ~spl8_54 | ~spl8_55 | ~spl8_56 | ~spl8_138)),
% 3.16/0.78    inference(subsumption_resolution,[],[f4001,f527])).
% 3.16/0.78  fof(f4001,plain,(
% 3.16/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl8_8 | ~spl8_9 | ~spl8_54 | ~spl8_55 | ~spl8_56 | ~spl8_138)),
% 3.16/0.78    inference(subsumption_resolution,[],[f4000,f221])).
% 3.16/0.78  fof(f4000,plain,(
% 3.16/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl8_8 | ~spl8_54 | ~spl8_55 | ~spl8_56 | ~spl8_138)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3999,f216])).
% 3.16/0.78  fof(f3999,plain,(
% 3.16/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl8_54 | ~spl8_55 | ~spl8_56 | ~spl8_138)),
% 3.16/0.78    inference(subsumption_resolution,[],[f1273,f2667])).
% 3.16/0.78  fof(f1273,plain,(
% 3.16/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl8_54 | ~spl8_55 | ~spl8_56)),
% 3.16/0.78    inference(subsumption_resolution,[],[f1272,f672])).
% 3.16/0.78  fof(f1272,plain,(
% 3.16/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl8_54 | ~spl8_55)),
% 3.16/0.78    inference(subsumption_resolution,[],[f1195,f667])).
% 3.16/0.78  fof(f667,plain,(
% 3.16/0.78    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl8_55),
% 3.16/0.78    inference(avatar_component_clause,[],[f665])).
% 3.16/0.78  fof(f1195,plain,(
% 3.16/0.78    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl8_54),
% 3.16/0.78    inference(resolution,[],[f662,f173])).
% 3.16/0.78  fof(f173,plain,(
% 3.16/0.78    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(duplicate_literal_removal,[],[f164])).
% 3.16/0.78  fof(f164,plain,(
% 3.16/0.78    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(equality_resolution,[],[f114])).
% 3.16/0.78  fof(f114,plain,(
% 3.16/0.78    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f70])).
% 3.16/0.78  fof(f662,plain,(
% 3.16/0.78    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl8_54),
% 3.16/0.78    inference(avatar_component_clause,[],[f660])).
% 3.16/0.78  fof(f3543,plain,(
% 3.16/0.78    ~spl8_44 | spl8_22 | ~spl8_35),
% 3.16/0.78    inference(avatar_split_clause,[],[f3001,f493,f361,f547])).
% 3.16/0.78  fof(f493,plain,(
% 3.16/0.78    spl8_35 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 3.16/0.78  fof(f3001,plain,(
% 3.16/0.78    v1_xboole_0(sK3) | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl8_35),
% 3.16/0.78    inference(resolution,[],[f495,f128])).
% 3.16/0.78  fof(f128,plain,(
% 3.16/0.78    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f50])).
% 3.16/0.78  fof(f50,plain,(
% 3.16/0.78    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.16/0.78    inference(ennf_transformation,[],[f19])).
% 3.16/0.78  fof(f19,axiom,(
% 3.16/0.78    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 3.16/0.78  fof(f495,plain,(
% 3.16/0.78    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl8_35),
% 3.16/0.78    inference(avatar_component_clause,[],[f493])).
% 3.16/0.78  fof(f3541,plain,(
% 3.16/0.78    ~spl8_44 | spl8_22 | ~spl8_3),
% 3.16/0.78    inference(avatar_split_clause,[],[f2066,f188,f361,f547])).
% 3.16/0.78  fof(f2066,plain,(
% 3.16/0.78    v1_xboole_0(sK3) | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl8_3),
% 3.16/0.78    inference(resolution,[],[f190,f128])).
% 3.16/0.78  fof(f3532,plain,(
% 3.16/0.78    ~spl8_37 | spl8_39 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_36 | ~spl8_38),
% 3.16/0.78    inference(avatar_split_clause,[],[f3531,f512,f504,f267,f229,f224,f198,f193,f188,f182,f516,f508])).
% 3.16/0.78  fof(f508,plain,(
% 3.16/0.78    spl8_37 <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 3.16/0.78  fof(f516,plain,(
% 3.16/0.78    spl8_39 <=> v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 3.16/0.78  fof(f267,plain,(
% 3.16/0.78    spl8_13 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 3.16/0.78  fof(f504,plain,(
% 3.16/0.78    spl8_36 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 3.16/0.78  fof(f512,plain,(
% 3.16/0.78    spl8_38 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 3.16/0.78  fof(f3531,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_36 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3530,f231])).
% 3.16/0.78  fof(f3530,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_13 | ~spl8_36 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3529,f226])).
% 3.16/0.78  fof(f3529,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_13 | ~spl8_36 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3528,f269])).
% 3.16/0.78  fof(f269,plain,(
% 3.16/0.78    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_13),
% 3.16/0.78    inference(avatar_component_clause,[],[f267])).
% 3.16/0.78  fof(f3528,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_36 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3527,f505])).
% 3.16/0.78  fof(f505,plain,(
% 3.16/0.78    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_36),
% 3.16/0.78    inference(avatar_component_clause,[],[f504])).
% 3.16/0.78  fof(f3527,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3526,f513])).
% 3.16/0.78  fof(f513,plain,(
% 3.16/0.78    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl8_38),
% 3.16/0.78    inference(avatar_component_clause,[],[f512])).
% 3.16/0.78  fof(f3526,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3525,f200])).
% 3.16/0.78  fof(f3525,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_2 | ~spl8_3 | ~spl8_4)),
% 3.16/0.78    inference(subsumption_resolution,[],[f498,f195])).
% 3.16/0.78  fof(f498,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_2 | ~spl8_3)),
% 3.16/0.78    inference(subsumption_resolution,[],[f462,f183])).
% 3.16/0.78  fof(f462,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl8_3),
% 3.16/0.78    inference(resolution,[],[f190,f175])).
% 3.16/0.78  fof(f3477,plain,(
% 3.16/0.78    ~spl8_37 | ~spl8_1 | spl8_39 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_38),
% 3.16/0.78    inference(avatar_split_clause,[],[f3476,f512,f229,f224,f219,f214,f208,f203,f198,f516,f178,f508])).
% 3.16/0.78  fof(f3476,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3475,f231])).
% 3.16/0.78  fof(f3475,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3474,f226])).
% 3.16/0.78  fof(f3474,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3473,f221])).
% 3.16/0.78  fof(f3473,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3472,f216])).
% 3.16/0.78  fof(f3472,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3471,f210])).
% 3.16/0.78  fof(f3471,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_5 | ~spl8_6 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3470,f205])).
% 3.16/0.78  fof(f3470,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_5 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3365,f200])).
% 3.16/0.78  fof(f3365,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl8_38),
% 3.16/0.78    inference(resolution,[],[f513,f174])).
% 3.16/0.78  fof(f3469,plain,(
% 3.16/0.78    ~spl8_37 | ~spl8_39 | spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_36 | ~spl8_38),
% 3.16/0.78    inference(avatar_split_clause,[],[f3468,f512,f504,f267,f229,f224,f198,f193,f188,f182,f516,f508])).
% 3.16/0.78  fof(f3468,plain,(
% 3.16/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_36 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3467,f231])).
% 3.16/0.78  fof(f3467,plain,(
% 3.16/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_13 | ~spl8_36 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3466,f226])).
% 3.16/0.78  fof(f3466,plain,(
% 3.16/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_13 | ~spl8_36 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3465,f269])).
% 3.16/0.78  fof(f3465,plain,(
% 3.16/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_36 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3464,f505])).
% 3.16/0.78  fof(f3464,plain,(
% 3.16/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3463,f513])).
% 3.16/0.78  fof(f3463,plain,(
% 3.16/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_3 | ~spl8_4 | ~spl8_5)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3462,f200])).
% 3.16/0.78  fof(f3462,plain,(
% 3.16/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_3 | ~spl8_4)),
% 3.16/0.78    inference(subsumption_resolution,[],[f1115,f195])).
% 3.16/0.78  fof(f1115,plain,(
% 3.16/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl8_3),
% 3.16/0.78    inference(resolution,[],[f190,f176])).
% 3.16/0.78  fof(f3409,plain,(
% 3.16/0.78    ~spl8_37 | ~spl8_39 | spl8_1 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_38),
% 3.16/0.78    inference(avatar_split_clause,[],[f3408,f512,f229,f224,f219,f214,f208,f203,f198,f178,f516,f508])).
% 3.16/0.78  fof(f3408,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,sK1) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3407,f231])).
% 3.16/0.78  fof(f3407,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,sK1) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3406,f226])).
% 3.16/0.78  fof(f3406,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,sK1) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3405,f221])).
% 3.16/0.78  fof(f3405,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,sK1) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3404,f216])).
% 3.16/0.78  fof(f3404,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,sK1) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3403,f210])).
% 3.16/0.78  fof(f3403,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,sK1) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_5 | ~spl8_6 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3402,f205])).
% 3.16/0.78  fof(f3402,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,sK1) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_5 | ~spl8_38)),
% 3.16/0.78    inference(subsumption_resolution,[],[f3366,f200])).
% 3.16/0.78  fof(f3366,plain,(
% 3.16/0.78    v5_pre_topc(sK3,sK0,sK1) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl8_38),
% 3.16/0.78    inference(resolution,[],[f513,f173])).
% 3.16/0.78  fof(f3353,plain,(
% 3.16/0.78    spl8_38 | ~spl8_3 | ~spl8_91),
% 3.16/0.78    inference(avatar_split_clause,[],[f3330,f1347,f188,f512])).
% 3.16/0.78  fof(f1347,plain,(
% 3.16/0.78    spl8_91 <=> r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).
% 3.16/0.78  fof(f3330,plain,(
% 3.16/0.78    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl8_3 | ~spl8_91)),
% 3.16/0.78    inference(resolution,[],[f1349,f469])).
% 3.16/0.78  fof(f469,plain,(
% 3.16/0.78    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) ) | ~spl8_3),
% 3.16/0.78    inference(resolution,[],[f190,f157])).
% 3.16/0.78  fof(f157,plain,(
% 3.16/0.78    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.16/0.78    inference(cnf_transformation,[],[f62])).
% 3.16/0.78  fof(f62,plain,(
% 3.16/0.78    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.16/0.78    inference(flattening,[],[f61])).
% 3.16/0.78  fof(f61,plain,(
% 3.16/0.78    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.16/0.78    inference(ennf_transformation,[],[f20])).
% 3.16/0.78  fof(f20,axiom,(
% 3.16/0.78    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 3.16/0.78  fof(f1349,plain,(
% 3.16/0.78    r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) | ~spl8_91),
% 3.16/0.78    inference(avatar_component_clause,[],[f1347])).
% 3.16/0.78  fof(f3277,plain,(
% 3.16/0.78    spl8_141 | ~spl8_5 | ~spl8_17 | ~spl8_51),
% 3.16/0.78    inference(avatar_split_clause,[],[f3254,f634,f333,f198,f2440])).
% 3.16/0.78  fof(f2440,plain,(
% 3.16/0.78    spl8_141 <=> v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_141])])).
% 3.16/0.78  fof(f333,plain,(
% 3.16/0.78    spl8_17 <=> v1_relat_1(sK3)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 3.16/0.78  fof(f634,plain,(
% 3.16/0.78    spl8_51 <=> r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 3.16/0.78  fof(f3254,plain,(
% 3.16/0.78    v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK1)) | (~spl8_5 | ~spl8_17 | ~spl8_51)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f335,f200,f636,f131])).
% 3.16/0.78  fof(f131,plain,(
% 3.16/0.78    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f53])).
% 3.16/0.78  fof(f53,plain,(
% 3.16/0.78    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.16/0.78    inference(flattening,[],[f52])).
% 3.16/0.78  fof(f52,plain,(
% 3.16/0.78    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.16/0.78    inference(ennf_transformation,[],[f25])).
% 3.16/0.78  fof(f25,axiom,(
% 3.16/0.78    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 3.16/0.78  fof(f636,plain,(
% 3.16/0.78    r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) | ~spl8_51),
% 3.16/0.78    inference(avatar_component_clause,[],[f634])).
% 3.16/0.78  fof(f335,plain,(
% 3.16/0.78    v1_relat_1(sK3) | ~spl8_17),
% 3.16/0.78    inference(avatar_component_clause,[],[f333])).
% 3.16/0.78  fof(f3207,plain,(
% 3.16/0.78    spl8_169 | ~spl8_59 | ~spl8_138),
% 3.16/0.78    inference(avatar_split_clause,[],[f3186,f2406,f685,f3107])).
% 3.16/0.78  fof(f3107,plain,(
% 3.16/0.78    spl8_169 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_169])])).
% 3.16/0.78  fof(f685,plain,(
% 3.16/0.78    spl8_59 <=> v1_relat_1(k1_xboole_0)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).
% 3.16/0.78  fof(f3186,plain,(
% 3.16/0.78    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl8_59 | ~spl8_138)),
% 3.16/0.78    inference(resolution,[],[f3083,f119])).
% 3.16/0.78  fof(f3083,plain,(
% 3.16/0.78    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) ) | (~spl8_59 | ~spl8_138)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f2972,f146])).
% 3.16/0.78  fof(f146,plain,(
% 3.16/0.78    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f57])).
% 3.16/0.78  fof(f57,plain,(
% 3.16/0.78    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.16/0.78    inference(ennf_transformation,[],[f16])).
% 3.16/0.78  fof(f16,axiom,(
% 3.16/0.78    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 3.16/0.78  fof(f2972,plain,(
% 3.16/0.78    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) ) | (~spl8_59 | ~spl8_138)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f687,f2940,f126])).
% 3.16/0.78  fof(f126,plain,(
% 3.16/0.78    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f79])).
% 3.16/0.78  fof(f79,plain,(
% 3.16/0.78    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.16/0.78    inference(nnf_transformation,[],[f49])).
% 3.16/0.78  fof(f49,plain,(
% 3.16/0.78    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.16/0.78    inference(ennf_transformation,[],[f13])).
% 3.16/0.78  fof(f13,axiom,(
% 3.16/0.78    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 3.16/0.78  fof(f2940,plain,(
% 3.16/0.78    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) ) | ~spl8_138),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f2667,f154])).
% 3.16/0.78  fof(f154,plain,(
% 3.16/0.78    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/0.78    inference(cnf_transformation,[],[f59])).
% 3.16/0.78  fof(f59,plain,(
% 3.16/0.78    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.78    inference(ennf_transformation,[],[f18])).
% 3.16/0.78  fof(f18,axiom,(
% 3.16/0.78    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.16/0.78  fof(f687,plain,(
% 3.16/0.78    v1_relat_1(k1_xboole_0) | ~spl8_59),
% 3.16/0.78    inference(avatar_component_clause,[],[f685])).
% 3.16/0.78  fof(f3173,plain,(
% 3.16/0.78    spl8_173 | ~spl8_59 | ~spl8_138),
% 3.16/0.78    inference(avatar_split_clause,[],[f3144,f2406,f685,f3164])).
% 3.16/0.78  fof(f3164,plain,(
% 3.16/0.78    spl8_173 <=> k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_173])])).
% 3.16/0.78  fof(f3144,plain,(
% 3.16/0.78    k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) | (~spl8_59 | ~spl8_138)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f2972,f2981,f137])).
% 3.16/0.78  fof(f137,plain,(
% 3.16/0.78    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f82])).
% 3.16/0.78  fof(f82,plain,(
% 3.16/0.78    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/0.78    inference(flattening,[],[f81])).
% 3.16/0.78  fof(f81,plain,(
% 3.16/0.78    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/0.78    inference(nnf_transformation,[],[f6])).
% 3.16/0.78  fof(f6,axiom,(
% 3.16/0.78    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.16/0.78  fof(f2981,plain,(
% 3.16/0.78    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0)) ) | (~spl8_59 | ~spl8_138)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f687,f2941,f124])).
% 3.16/0.78  fof(f124,plain,(
% 3.16/0.78    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f78])).
% 3.16/0.78  fof(f78,plain,(
% 3.16/0.78    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.16/0.78    inference(nnf_transformation,[],[f48])).
% 3.16/0.78  fof(f48,plain,(
% 3.16/0.78    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.16/0.78    inference(ennf_transformation,[],[f14])).
% 3.16/0.78  fof(f14,axiom,(
% 3.16/0.78    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 3.16/0.78  fof(f2941,plain,(
% 3.16/0.78    ( ! [X0] : (v5_relat_1(k1_xboole_0,X0)) ) | ~spl8_138),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f2667,f155])).
% 3.16/0.78  fof(f155,plain,(
% 3.16/0.78    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/0.78    inference(cnf_transformation,[],[f59])).
% 3.16/0.78  fof(f2860,plain,(
% 3.16/0.78    spl8_158 | ~spl8_59 | ~spl8_78 | ~spl8_86),
% 3.16/0.78    inference(avatar_split_clause,[],[f2859,f1282,f1223,f685,f2854])).
% 3.16/0.78  fof(f2854,plain,(
% 3.16/0.78    spl8_158 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_158])])).
% 3.16/0.78  fof(f1223,plain,(
% 3.16/0.78    spl8_78 <=> v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).
% 3.16/0.78  fof(f2859,plain,(
% 3.16/0.78    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | (~spl8_59 | ~spl8_78 | ~spl8_86)),
% 3.16/0.78    inference(subsumption_resolution,[],[f2858,f687])).
% 3.16/0.78  fof(f2858,plain,(
% 3.16/0.78    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl8_78 | ~spl8_86)),
% 3.16/0.78    inference(subsumption_resolution,[],[f2848,f1225])).
% 3.16/0.78  fof(f1225,plain,(
% 3.16/0.78    v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl8_78),
% 3.16/0.78    inference(avatar_component_clause,[],[f1223])).
% 3.16/0.78  fof(f2848,plain,(
% 3.16/0.78    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_relat_1(k1_xboole_0) | ~spl8_86),
% 3.16/0.78    inference(resolution,[],[f1284,f133])).
% 3.16/0.78  fof(f133,plain,(
% 3.16/0.78    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f80])).
% 3.16/0.78  fof(f80,plain,(
% 3.16/0.78    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/0.78    inference(nnf_transformation,[],[f55])).
% 3.16/0.78  fof(f55,plain,(
% 3.16/0.78    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/0.78    inference(flattening,[],[f54])).
% 3.16/0.78  fof(f54,plain,(
% 3.16/0.78    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.16/0.78    inference(ennf_transformation,[],[f23])).
% 3.16/0.78  fof(f23,axiom,(
% 3.16/0.78    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 3.16/0.78  fof(f1284,plain,(
% 3.16/0.78    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl8_86),
% 3.16/0.78    inference(avatar_component_clause,[],[f1282])).
% 3.16/0.78  fof(f2740,plain,(
% 3.16/0.78    spl8_78 | ~spl8_54),
% 3.16/0.78    inference(avatar_split_clause,[],[f2724,f660,f1223])).
% 3.16/0.78  fof(f2724,plain,(
% 3.16/0.78    v4_relat_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl8_54),
% 3.16/0.78    inference(resolution,[],[f662,f154])).
% 3.16/0.78  fof(f2689,plain,(
% 3.16/0.78    spl8_54 | ~spl8_138),
% 3.16/0.78    inference(avatar_contradiction_clause,[],[f2668])).
% 3.16/0.78  fof(f2668,plain,(
% 3.16/0.78    $false | (spl8_54 | ~spl8_138)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f661,f2539,f142])).
% 3.16/0.78  fof(f661,plain,(
% 3.16/0.78    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | spl8_54),
% 3.16/0.78    inference(avatar_component_clause,[],[f660])).
% 3.16/0.78  fof(f2613,plain,(
% 3.16/0.78    spl8_59 | ~spl8_57),
% 3.16/0.78    inference(avatar_split_clause,[],[f2600,f675,f685])).
% 3.16/0.78  fof(f2600,plain,(
% 3.16/0.78    v1_relat_1(k1_xboole_0) | ~spl8_57),
% 3.16/0.78    inference(resolution,[],[f677,f153])).
% 3.16/0.78  fof(f153,plain,(
% 3.16/0.78    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/0.78    inference(cnf_transformation,[],[f58])).
% 3.16/0.78  fof(f58,plain,(
% 3.16/0.78    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/0.78    inference(ennf_transformation,[],[f17])).
% 3.16/0.78  fof(f17,axiom,(
% 3.16/0.78    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.16/0.78  fof(f2553,plain,(
% 3.16/0.78    spl8_67 | ~spl8_138),
% 3.16/0.78    inference(avatar_contradiction_clause,[],[f2540])).
% 3.16/0.78  fof(f2540,plain,(
% 3.16/0.78    $false | (spl8_67 | ~spl8_138)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f918,f2515,f139])).
% 3.16/0.78  fof(f918,plain,(
% 3.16/0.78    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | spl8_67),
% 3.16/0.78    inference(avatar_component_clause,[],[f917])).
% 3.16/0.78  fof(f917,plain,(
% 3.16/0.78    spl8_67 <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).
% 3.16/0.78  fof(f2533,plain,(
% 3.16/0.78    u1_struct_0(sK0) != k1_relat_1(sK3) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK3) | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.16/0.78    introduced(theory_tautology_sat_conflict,[])).
% 3.16/0.78  fof(f2532,plain,(
% 3.16/0.78    spl8_147 | ~spl8_17 | ~spl8_34 | ~spl8_45),
% 3.16/0.78    inference(avatar_split_clause,[],[f2531,f551,f488,f333,f2526])).
% 3.16/0.78  fof(f2526,plain,(
% 3.16/0.78    spl8_147 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).
% 3.16/0.78  fof(f488,plain,(
% 3.16/0.78    spl8_34 <=> v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 3.16/0.78  fof(f551,plain,(
% 3.16/0.78    spl8_45 <=> v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 3.16/0.78  fof(f2531,plain,(
% 3.16/0.78    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) | (~spl8_17 | ~spl8_34 | ~spl8_45)),
% 3.16/0.78    inference(subsumption_resolution,[],[f2530,f335])).
% 3.16/0.78  fof(f2530,plain,(
% 3.16/0.78    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl8_34 | ~spl8_45)),
% 3.16/0.78    inference(subsumption_resolution,[],[f2524,f490])).
% 3.16/0.78  fof(f490,plain,(
% 3.16/0.78    v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl8_34),
% 3.16/0.78    inference(avatar_component_clause,[],[f488])).
% 3.16/0.78  fof(f2524,plain,(
% 3.16/0.78    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) | ~v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_relat_1(sK3) | ~spl8_45),
% 3.16/0.78    inference(resolution,[],[f553,f133])).
% 3.16/0.78  fof(f553,plain,(
% 3.16/0.78    v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl8_45),
% 3.16/0.78    inference(avatar_component_clause,[],[f551])).
% 3.16/0.78  fof(f2457,plain,(
% 3.16/0.78    spl8_138),
% 3.16/0.78    inference(avatar_contradiction_clause,[],[f2456])).
% 3.16/0.78  fof(f2456,plain,(
% 3.16/0.78    $false | spl8_138),
% 3.16/0.78    inference(subsumption_resolution,[],[f2448,f170])).
% 3.16/0.78  fof(f170,plain,(
% 3.16/0.78    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.16/0.78    inference(equality_resolution,[],[f135])).
% 3.16/0.78  fof(f135,plain,(
% 3.16/0.78    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.16/0.78    inference(cnf_transformation,[],[f82])).
% 3.16/0.78  fof(f2448,plain,(
% 3.16/0.78    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl8_138),
% 3.16/0.78    inference(resolution,[],[f2408,f142])).
% 3.16/0.78  fof(f2408,plain,(
% 3.16/0.78    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl8_138),
% 3.16/0.78    inference(avatar_component_clause,[],[f2406])).
% 3.16/0.78  fof(f2324,plain,(
% 3.16/0.78    spl8_45 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_44),
% 3.16/0.78    inference(avatar_split_clause,[],[f2313,f547,f198,f193,f188,f551])).
% 3.16/0.78  fof(f2200,plain,(
% 3.16/0.78    ~spl8_14 | spl8_40),
% 3.16/0.78    inference(avatar_split_clause,[],[f2198,f526,f283])).
% 3.16/0.78  fof(f283,plain,(
% 3.16/0.78    spl8_14 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 3.16/0.78  fof(f2198,plain,(
% 3.16/0.78    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl8_40),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f528,f129])).
% 3.16/0.78  fof(f129,plain,(
% 3.16/0.78    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.16/0.78    inference(cnf_transformation,[],[f51])).
% 3.16/0.78  fof(f51,plain,(
% 3.16/0.78    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.16/0.78    inference(ennf_transformation,[],[f34])).
% 3.16/0.78  fof(f34,plain,(
% 3.16/0.78    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 3.16/0.78    inference(pure_predicate_removal,[],[f26])).
% 3.16/0.78  fof(f26,axiom,(
% 3.16/0.78    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 3.16/0.78  fof(f528,plain,(
% 3.16/0.78    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl8_40),
% 3.16/0.78    inference(avatar_component_clause,[],[f526])).
% 3.16/0.78  fof(f2089,plain,(
% 3.16/0.78    spl8_34 | ~spl8_3),
% 3.16/0.78    inference(avatar_split_clause,[],[f2063,f188,f488])).
% 3.16/0.78  fof(f2063,plain,(
% 3.16/0.78    v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl8_3),
% 3.16/0.78    inference(resolution,[],[f190,f154])).
% 3.16/0.78  fof(f2075,plain,(
% 3.16/0.78    spl8_35 | ~spl8_3),
% 3.16/0.78    inference(avatar_split_clause,[],[f2047,f188,f493])).
% 3.16/0.78  fof(f2047,plain,(
% 3.16/0.78    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl8_3),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f170,f190,f157])).
% 3.16/0.78  fof(f1963,plain,(
% 3.16/0.78    ~spl8_67 | spl8_57),
% 3.16/0.78    inference(avatar_split_clause,[],[f1956,f675,f917])).
% 3.16/0.78  fof(f1956,plain,(
% 3.16/0.78    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | spl8_57),
% 3.16/0.78    inference(resolution,[],[f676,f142])).
% 3.16/0.78  fof(f676,plain,(
% 3.16/0.78    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl8_57),
% 3.16/0.78    inference(avatar_component_clause,[],[f675])).
% 3.16/0.78  fof(f1953,plain,(
% 3.16/0.78    spl8_51 | ~spl8_17 | ~spl8_18),
% 3.16/0.78    inference(avatar_split_clause,[],[f1951,f338,f333,f634])).
% 3.16/0.78  fof(f338,plain,(
% 3.16/0.78    spl8_18 <=> v5_relat_1(sK3,u1_struct_0(sK1))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 3.16/0.78  fof(f1951,plain,(
% 3.16/0.78    r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) | (~spl8_17 | ~spl8_18)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f335,f340,f124])).
% 3.16/0.78  fof(f340,plain,(
% 3.16/0.78    v5_relat_1(sK3,u1_struct_0(sK1)) | ~spl8_18),
% 3.16/0.78    inference(avatar_component_clause,[],[f338])).
% 3.16/0.78  fof(f1948,plain,(
% 3.16/0.78    spl8_18 | ~spl8_6),
% 3.16/0.78    inference(avatar_split_clause,[],[f1938,f203,f338])).
% 3.16/0.78  fof(f1938,plain,(
% 3.16/0.78    v5_relat_1(sK3,u1_struct_0(sK1)) | ~spl8_6),
% 3.16/0.78    inference(resolution,[],[f205,f155])).
% 3.16/0.78  fof(f1752,plain,(
% 3.16/0.78    ~spl8_12 | spl8_36),
% 3.16/0.78    inference(avatar_split_clause,[],[f1750,f504,f252])).
% 3.16/0.78  fof(f252,plain,(
% 3.16/0.78    spl8_12 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 3.16/0.78  fof(f1750,plain,(
% 3.16/0.78    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl8_36),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f506,f129])).
% 3.16/0.78  fof(f506,plain,(
% 3.16/0.78    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl8_36),
% 3.16/0.78    inference(avatar_component_clause,[],[f504])).
% 3.16/0.78  fof(f1695,plain,(
% 3.16/0.78    spl8_94 | ~spl8_17 | ~spl8_19 | ~spl8_23),
% 3.16/0.78    inference(avatar_split_clause,[],[f1694,f368,f343,f333,f1375])).
% 3.16/0.78  fof(f1375,plain,(
% 3.16/0.78    spl8_94 <=> u1_struct_0(sK0) = k1_relat_1(sK3)),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).
% 3.16/0.78  fof(f343,plain,(
% 3.16/0.78    spl8_19 <=> v4_relat_1(sK3,u1_struct_0(sK0))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 3.16/0.78  fof(f1694,plain,(
% 3.16/0.78    u1_struct_0(sK0) = k1_relat_1(sK3) | (~spl8_17 | ~spl8_19 | ~spl8_23)),
% 3.16/0.78    inference(subsumption_resolution,[],[f1693,f335])).
% 3.16/0.78  fof(f1693,plain,(
% 3.16/0.78    u1_struct_0(sK0) = k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl8_19 | ~spl8_23)),
% 3.16/0.78    inference(subsumption_resolution,[],[f1691,f345])).
% 3.16/0.78  fof(f345,plain,(
% 3.16/0.78    v4_relat_1(sK3,u1_struct_0(sK0)) | ~spl8_19),
% 3.16/0.78    inference(avatar_component_clause,[],[f343])).
% 3.16/0.78  fof(f1691,plain,(
% 3.16/0.78    u1_struct_0(sK0) = k1_relat_1(sK3) | ~v4_relat_1(sK3,u1_struct_0(sK0)) | ~v1_relat_1(sK3) | ~spl8_23),
% 3.16/0.78    inference(resolution,[],[f370,f133])).
% 3.16/0.78  fof(f370,plain,(
% 3.16/0.78    v1_partfun1(sK3,u1_struct_0(sK0)) | ~spl8_23),
% 3.16/0.78    inference(avatar_component_clause,[],[f368])).
% 3.16/0.78  fof(f1641,plain,(
% 3.16/0.78    ~spl8_21 | ~spl8_6 | spl8_22),
% 3.16/0.78    inference(avatar_split_clause,[],[f1632,f361,f203,f357])).
% 3.16/0.78  fof(f1632,plain,(
% 3.16/0.78    ~v1_xboole_0(u1_struct_0(sK1)) | (~spl8_6 | spl8_22)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f205,f362,f128])).
% 3.16/0.78  fof(f362,plain,(
% 3.16/0.78    ~v1_xboole_0(sK3) | spl8_22),
% 3.16/0.78    inference(avatar_component_clause,[],[f361])).
% 3.16/0.78  fof(f1350,plain,(
% 3.16/0.78    spl8_91 | ~spl8_17 | ~spl8_19),
% 3.16/0.78    inference(avatar_split_clause,[],[f1343,f343,f333,f1347])).
% 3.16/0.78  fof(f1343,plain,(
% 3.16/0.78    r1_tarski(k1_relat_1(sK3),u1_struct_0(sK0)) | (~spl8_17 | ~spl8_19)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f335,f345,f126])).
% 3.16/0.78  fof(f886,plain,(
% 3.16/0.78    spl8_19 | ~spl8_6),
% 3.16/0.78    inference(avatar_split_clause,[],[f874,f203,f343])).
% 3.16/0.78  fof(f874,plain,(
% 3.16/0.78    v4_relat_1(sK3,u1_struct_0(sK0)) | ~spl8_6),
% 3.16/0.78    inference(resolution,[],[f205,f154])).
% 3.16/0.78  fof(f775,plain,(
% 3.16/0.78    spl8_55 | ~spl8_4 | ~spl8_30),
% 3.16/0.78    inference(avatar_split_clause,[],[f641,f445,f193,f665])).
% 3.16/0.78  fof(f641,plain,(
% 3.16/0.78    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl8_4 | ~spl8_30)),
% 3.16/0.78    inference(backward_demodulation,[],[f195,f447])).
% 3.16/0.78  fof(f772,plain,(
% 3.16/0.78    spl8_58 | ~spl8_7 | ~spl8_30),
% 3.16/0.78    inference(avatar_split_clause,[],[f644,f445,f208,f680])).
% 3.16/0.78  fof(f644,plain,(
% 3.16/0.78    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl8_7 | ~spl8_30)),
% 3.16/0.78    inference(backward_demodulation,[],[f210,f447])).
% 3.16/0.78  fof(f726,plain,(
% 3.16/0.78    spl8_27 | ~spl8_5 | ~spl8_17),
% 3.16/0.78    inference(avatar_split_clause,[],[f711,f333,f198,f404])).
% 3.16/0.78  fof(f404,plain,(
% 3.16/0.78    spl8_27 <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 3.16/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 3.16/0.78  fof(f711,plain,(
% 3.16/0.78    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | (~spl8_5 | ~spl8_17)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f200,f170,f335,f131])).
% 3.16/0.78  fof(f355,plain,(
% 3.16/0.78    spl8_17 | ~spl8_6),
% 3.16/0.78    inference(avatar_split_clause,[],[f322,f203,f333])).
% 3.16/0.78  fof(f322,plain,(
% 3.16/0.78    v1_relat_1(sK3) | ~spl8_6),
% 3.16/0.78    inference(resolution,[],[f205,f153])).
% 3.16/0.78  fof(f301,plain,(
% 3.16/0.78    spl8_15 | ~spl8_10 | ~spl8_11),
% 3.16/0.78    inference(avatar_split_clause,[],[f287,f229,f224,f298])).
% 3.16/0.78  fof(f287,plain,(
% 3.16/0.78    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl8_10 | ~spl8_11)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f226,f231,f112])).
% 3.16/0.78  fof(f112,plain,(
% 3.16/0.78    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f40])).
% 3.16/0.78  fof(f40,plain,(
% 3.16/0.78    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.16/0.78    inference(flattening,[],[f39])).
% 3.16/0.78  fof(f39,plain,(
% 3.16/0.78    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.16/0.78    inference(ennf_transformation,[],[f33])).
% 3.16/0.78  fof(f33,plain,(
% 3.16/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.16/0.78    inference(pure_predicate_removal,[],[f28])).
% 3.16/0.78  fof(f28,axiom,(
% 3.16/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 3.16/0.78  fof(f286,plain,(
% 3.16/0.78    spl8_14 | ~spl8_10),
% 3.16/0.78    inference(avatar_split_clause,[],[f271,f224,f283])).
% 3.16/0.78  fof(f271,plain,(
% 3.16/0.78    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl8_10),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f226,f111])).
% 3.16/0.78  fof(f111,plain,(
% 3.16/0.78    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.16/0.78    inference(cnf_transformation,[],[f38])).
% 3.16/0.78  fof(f38,plain,(
% 3.16/0.78    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.16/0.78    inference(ennf_transformation,[],[f27])).
% 3.16/0.78  fof(f27,axiom,(
% 3.16/0.78    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 3.16/0.78  fof(f270,plain,(
% 3.16/0.78    spl8_13 | ~spl8_8 | ~spl8_9),
% 3.16/0.78    inference(avatar_split_clause,[],[f256,f219,f214,f267])).
% 3.16/0.78  fof(f256,plain,(
% 3.16/0.78    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl8_8 | ~spl8_9)),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f216,f221,f112])).
% 3.16/0.78  fof(f255,plain,(
% 3.16/0.78    spl8_12 | ~spl8_8),
% 3.16/0.78    inference(avatar_split_clause,[],[f240,f214,f252])).
% 3.16/0.78  fof(f240,plain,(
% 3.16/0.78    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl8_8),
% 3.16/0.78    inference(unit_resulting_resolution,[],[f216,f111])).
% 3.16/0.78  fof(f232,plain,(
% 3.16/0.78    spl8_11),
% 3.16/0.78    inference(avatar_split_clause,[],[f92,f229])).
% 3.16/0.78  fof(f92,plain,(
% 3.16/0.78    v2_pre_topc(sK0)),
% 3.16/0.78    inference(cnf_transformation,[],[f69])).
% 3.16/0.78  fof(f69,plain,(
% 3.16/0.78    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.16/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f64,f68,f67,f66,f65])).
% 3.16/0.78  fof(f65,plain,(
% 3.16/0.78    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.16/0.78    introduced(choice_axiom,[])).
% 3.16/0.78  fof(f66,plain,(
% 3.16/0.78    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.16/0.78    introduced(choice_axiom,[])).
% 3.16/0.78  fof(f67,plain,(
% 3.16/0.78    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 3.16/0.78    introduced(choice_axiom,[])).
% 3.16/0.78  fof(f68,plain,(
% 3.16/0.78    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 3.16/0.78    introduced(choice_axiom,[])).
% 3.16/0.78  fof(f64,plain,(
% 3.16/0.78    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.16/0.78    inference(flattening,[],[f63])).
% 3.16/0.78  fof(f63,plain,(
% 3.16/0.78    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.16/0.78    inference(nnf_transformation,[],[f36])).
% 3.16/0.78  fof(f36,plain,(
% 3.16/0.78    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.16/0.78    inference(flattening,[],[f35])).
% 3.16/0.78  fof(f35,plain,(
% 3.16/0.78    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.16/0.78    inference(ennf_transformation,[],[f32])).
% 3.16/0.78  fof(f32,negated_conjecture,(
% 3.16/0.78    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.16/0.78    inference(negated_conjecture,[],[f31])).
% 3.16/0.78  fof(f31,conjecture,(
% 3.16/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.16/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).
% 3.16/0.78  fof(f227,plain,(
% 3.16/0.78    spl8_10),
% 3.16/0.78    inference(avatar_split_clause,[],[f93,f224])).
% 3.16/0.78  fof(f93,plain,(
% 3.16/0.78    l1_pre_topc(sK0)),
% 3.16/0.78    inference(cnf_transformation,[],[f69])).
% 3.16/0.78  fof(f222,plain,(
% 3.16/0.78    spl8_9),
% 3.16/0.78    inference(avatar_split_clause,[],[f94,f219])).
% 3.16/0.78  fof(f94,plain,(
% 3.16/0.78    v2_pre_topc(sK1)),
% 3.16/0.78    inference(cnf_transformation,[],[f69])).
% 3.16/0.78  fof(f217,plain,(
% 3.16/0.78    spl8_8),
% 3.16/0.78    inference(avatar_split_clause,[],[f95,f214])).
% 3.16/0.78  fof(f95,plain,(
% 3.16/0.78    l1_pre_topc(sK1)),
% 3.16/0.78    inference(cnf_transformation,[],[f69])).
% 3.16/0.78  fof(f212,plain,(
% 3.16/0.78    spl8_5),
% 3.16/0.78    inference(avatar_split_clause,[],[f162,f198])).
% 3.16/0.78  fof(f162,plain,(
% 3.16/0.78    v1_funct_1(sK3)),
% 3.16/0.78    inference(definition_unfolding,[],[f96,f102])).
% 3.16/0.78  fof(f102,plain,(
% 3.16/0.78    sK2 = sK3),
% 3.16/0.78    inference(cnf_transformation,[],[f69])).
% 3.16/0.78  fof(f96,plain,(
% 3.16/0.78    v1_funct_1(sK2)),
% 3.16/0.78    inference(cnf_transformation,[],[f69])).
% 3.16/0.78  fof(f211,plain,(
% 3.16/0.78    spl8_7),
% 3.16/0.78    inference(avatar_split_clause,[],[f161,f208])).
% 3.16/0.78  fof(f161,plain,(
% 3.16/0.78    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.16/0.78    inference(definition_unfolding,[],[f97,f102])).
% 3.16/0.78  fof(f97,plain,(
% 3.16/0.78    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.16/0.78    inference(cnf_transformation,[],[f69])).
% 3.16/0.78  fof(f206,plain,(
% 3.16/0.78    spl8_6),
% 3.16/0.78    inference(avatar_split_clause,[],[f160,f203])).
% 3.16/0.78  fof(f160,plain,(
% 3.16/0.78    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.16/0.78    inference(definition_unfolding,[],[f98,f102])).
% 3.16/0.78  fof(f98,plain,(
% 3.16/0.78    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.16/0.78    inference(cnf_transformation,[],[f69])).
% 3.16/0.78  fof(f196,plain,(
% 3.16/0.78    spl8_4),
% 3.16/0.78    inference(avatar_split_clause,[],[f100,f193])).
% 3.16/0.78  fof(f100,plain,(
% 3.16/0.78    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.16/0.78    inference(cnf_transformation,[],[f69])).
% 3.16/0.78  fof(f191,plain,(
% 3.16/0.78    spl8_3),
% 3.16/0.78    inference(avatar_split_clause,[],[f101,f188])).
% 3.16/0.78  fof(f101,plain,(
% 3.16/0.78    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.16/0.78    inference(cnf_transformation,[],[f69])).
% 3.16/0.78  fof(f186,plain,(
% 3.16/0.78    spl8_1 | spl8_2),
% 3.16/0.78    inference(avatar_split_clause,[],[f159,f182,f178])).
% 3.16/0.78  fof(f159,plain,(
% 3.16/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK3,sK0,sK1)),
% 3.16/0.78    inference(definition_unfolding,[],[f103,f102])).
% 3.16/0.78  fof(f103,plain,(
% 3.16/0.78    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.16/0.78    inference(cnf_transformation,[],[f69])).
% 3.16/0.78  fof(f185,plain,(
% 3.16/0.78    ~spl8_1 | ~spl8_2),
% 3.16/0.78    inference(avatar_split_clause,[],[f158,f182,f178])).
% 3.16/0.78  fof(f158,plain,(
% 3.16/0.78    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,sK1)),
% 3.16/0.78    inference(definition_unfolding,[],[f104,f102])).
% 3.16/0.78  fof(f104,plain,(
% 3.16/0.78    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.16/0.78    inference(cnf_transformation,[],[f69])).
% 3.16/0.78  % SZS output end Proof for theBenchmark
% 3.16/0.78  % (25207)------------------------------
% 3.16/0.78  % (25207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.78  % (25207)Termination reason: Refutation
% 3.16/0.78  
% 3.16/0.78  % (25207)Memory used [KB]: 8955
% 3.16/0.78  % (25207)Time elapsed: 0.374 s
% 3.16/0.78  % (25207)------------------------------
% 3.16/0.78  % (25207)------------------------------
% 3.16/0.79  % (25181)Success in time 0.421 s
%------------------------------------------------------------------------------
