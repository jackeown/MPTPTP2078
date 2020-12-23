%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t32_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:38 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 213 expanded)
%              Number of leaves         :   20 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  367 ( 755 expanded)
%              Number of equality atoms :   15 (  46 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f117,f127,f131,f161,f170,f220,f229,f239,f441,f483,f874,f969,f1010,f1055,f1126])).

fof(f1126,plain,
    ( spl11_72
    | ~ spl11_18
    | ~ spl11_28
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f1125,f237,f218,f168,f481])).

fof(f481,plain,
    ( spl11_72
  <=> sP5(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_72])])).

fof(f168,plain,
    ( spl11_18
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f218,plain,
    ( spl11_28
  <=> k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f237,plain,
    ( spl11_34
  <=> r2_hidden(sK3,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f1125,plain,
    ( sP5(sK2,sK1,sK0)
    | ~ spl11_18
    | ~ spl11_28
    | ~ spl11_34 ),
    inference(superposition,[],[f1069,f219])).

fof(f219,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1)) = sK2
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f218])).

fof(f1069,plain,
    ( ! [X0] : sP5(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),X0,sK0)
    | ~ spl11_18
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f1060,f238])).

fof(f238,plain,
    ( r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f237])).

fof(f1060,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,u1_pre_topc(sK0))
        | sP5(k9_subset_1(u1_struct_0(X0),sK3,k2_struct_0(X0)),X0,sK0) )
    | ~ spl11_18 ),
    inference(resolution,[],[f169,f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | sP5(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1,X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | sP5(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',d9_pre_topc)).

fof(f169,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f1055,plain,
    ( ~ spl11_0
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | spl11_13
    | ~ spl11_72 ),
    inference(avatar_contradiction_clause,[],[f1054])).

fof(f1054,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_13
    | ~ spl11_72 ),
    inference(subsumption_resolution,[],[f1053,f116])).

fof(f116,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl11_4
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f1053,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_13
    | ~ spl11_72 ),
    inference(subsumption_resolution,[],[f1052,f105])).

fof(f105,plain,
    ( l1_pre_topc(sK0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl11_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f1052,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_13
    | ~ spl11_72 ),
    inference(resolution,[],[f1036,f482])).

fof(f482,plain,
    ( sP5(sK2,sK1,sK0)
    | ~ spl11_72 ),
    inference(avatar_component_clause,[],[f481])).

fof(f1036,plain,
    ( ! [X1] :
        ( ~ sP5(sK2,sK1,X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1) )
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f148,f230])).

fof(f230,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f146,f225])).

fof(f225,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl11_13
  <=> ~ v3_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f146,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | v3_pre_topc(sK2,sK1)
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f135,f126])).

fof(f126,plain,
    ( l1_pre_topc(sK1)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl11_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f135,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | v3_pre_topc(sK2,sK1)
    | ~ spl11_8 ),
    inference(resolution,[],[f130,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',d5_pre_topc)).

fof(f130,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl11_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f148,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ sP5(sK2,sK1,X1)
        | r2_hidden(sK2,u1_pre_topc(sK1))
        | ~ m1_pre_topc(sK1,X1) )
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f138,f126])).

fof(f138,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X1)
        | ~ sP5(sK2,sK1,X1)
        | r2_hidden(sK2,u1_pre_topc(sK1))
        | ~ m1_pre_topc(sK1,X1) )
    | ~ spl11_8 ),
    inference(resolution,[],[f130,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ sP5(X2,X1,X0)
      | r2_hidden(X2,u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1010,plain,
    ( ~ spl11_0
    | ~ spl11_30
    | ~ spl11_72
    | ~ spl11_120
    | ~ spl11_138 ),
    inference(avatar_contradiction_clause,[],[f1009])).

fof(f1009,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_30
    | ~ spl11_72
    | ~ spl11_120
    | ~ spl11_138 ),
    inference(subsumption_resolution,[],[f1008,f1006])).

fof(f1006,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl11_30
    | ~ spl11_72
    | ~ spl11_138 ),
    inference(subsumption_resolution,[],[f994,f493])).

fof(f493,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK6(sK0,sK1,sK2),k2_struct_0(sK1)) = sK2
    | ~ spl11_72 ),
    inference(resolution,[],[f482,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X2,X1,X0)
      | k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),k2_struct_0(X1)) = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f994,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK6(sK0,sK1,sK2),k2_struct_0(sK1)) != sK2
    | ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl11_30
    | ~ spl11_138 ),
    inference(resolution,[],[f968,f228])).

fof(f228,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl11_30
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f968,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_138 ),
    inference(avatar_component_clause,[],[f967])).

fof(f967,plain,
    ( spl11_138
  <=> m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_138])])).

fof(f1008,plain,
    ( v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl11_0
    | ~ spl11_120
    | ~ spl11_138 ),
    inference(subsumption_resolution,[],[f1007,f873])).

fof(f873,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),u1_pre_topc(sK0))
    | ~ spl11_120 ),
    inference(avatar_component_clause,[],[f872])).

fof(f872,plain,
    ( spl11_120
  <=> r2_hidden(sK6(sK0,sK1,sK2),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_120])])).

fof(f1007,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK2),u1_pre_topc(sK0))
    | v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl11_0
    | ~ spl11_138 ),
    inference(subsumption_resolution,[],[f995,f105])).

fof(f995,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK6(sK0,sK1,sK2),u1_pre_topc(sK0))
    | v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl11_138 ),
    inference(resolution,[],[f968,f81])).

fof(f969,plain,
    ( spl11_138
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f491,f481,f967])).

fof(f491,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_72 ),
    inference(resolution,[],[f482,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X2,X1,X0)
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f874,plain,
    ( spl11_120
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f492,f481,f872])).

fof(f492,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),u1_pre_topc(sK0))
    | ~ spl11_72 ),
    inference(resolution,[],[f482,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X2,X1,X0)
      | r2_hidden(sK6(X0,X1,X2),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f483,plain,
    ( spl11_72
    | ~ spl11_0
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f418,f190,f129,f125,f115,f104,f481])).

fof(f190,plain,
    ( spl11_24
  <=> r2_hidden(sK2,u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f418,plain,
    ( sP5(sK2,sK1,sK0)
    | ~ spl11_0
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f417,f105])).

fof(f417,plain,
    ( sP5(sK2,sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_24 ),
    inference(resolution,[],[f404,f116])).

fof(f404,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(sK1,X2)
        | sP5(sK2,sK1,X2)
        | ~ l1_pre_topc(X2) )
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f149,f191])).

fof(f191,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f190])).

fof(f149,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(X2)
        | sP5(sK2,sK1,X2)
        | ~ r2_hidden(sK2,u1_pre_topc(sK1))
        | ~ m1_pre_topc(sK1,X2) )
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f139,f126])).

fof(f139,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X2)
        | sP5(sK2,sK1,X2)
        | ~ r2_hidden(sK2,u1_pre_topc(sK1))
        | ~ m1_pre_topc(sK1,X2) )
    | ~ spl11_8 ),
    inference(resolution,[],[f130,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | sP5(X2,X1,X0)
      | ~ r2_hidden(X2,u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f441,plain,
    ( ~ spl11_13
    | ~ spl11_6
    | ~ spl11_8
    | spl11_25 ),
    inference(avatar_split_clause,[],[f440,f241,f129,f125,f224])).

fof(f241,plain,
    ( spl11_25
  <=> ~ r2_hidden(sK2,u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f440,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f147,f242])).

fof(f242,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f241])).

fof(f147,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ v3_pre_topc(sK2,sK1)
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f136,f126])).

fof(f136,plain,
    ( ~ l1_pre_topc(sK1)
    | r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ v3_pre_topc(sK2,sK1)
    | ~ spl11_8 ),
    inference(resolution,[],[f130,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f239,plain,
    ( spl11_34
    | ~ spl11_0
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f208,f168,f159,f104,f237])).

fof(f159,plain,
    ( spl11_14
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f208,plain,
    ( r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ spl11_0
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f207,f160])).

fof(f160,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f207,plain,
    ( r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ spl11_0
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f197,f105])).

fof(f197,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ spl11_18 ),
    inference(resolution,[],[f169,f82])).

fof(f229,plain,
    ( ~ spl11_13
    | spl11_30 ),
    inference(avatar_split_clause,[],[f58,f227,f224])).

fof(f58,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2
      | ~ v3_pre_topc(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_pre_topc(X2,X1)
              <~> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( v3_pre_topc(X2,X1)
                <=> ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',t32_tops_2)).

fof(f220,plain,
    ( spl11_12
    | spl11_28 ),
    inference(avatar_split_clause,[],[f61,f218,f156])).

fof(f156,plain,
    ( spl11_12
  <=> v3_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f61,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1)) = sK2
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f170,plain,
    ( spl11_12
    | spl11_18 ),
    inference(avatar_split_clause,[],[f59,f168,f156])).

fof(f59,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f161,plain,
    ( spl11_12
    | spl11_14 ),
    inference(avatar_split_clause,[],[f60,f159,f156])).

fof(f60,plain,
    ( v3_pre_topc(sK3,sK0)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f131,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f62,f129])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f127,plain,
    ( spl11_6
    | ~ spl11_0
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f121,f115,f104,f125])).

fof(f121,plain,
    ( l1_pre_topc(sK1)
    | ~ spl11_0
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f119,f105])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl11_4 ),
    inference(resolution,[],[f116,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',dt_m1_pre_topc)).

fof(f117,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f63,f115])).

fof(f63,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f106,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f64,f104])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
