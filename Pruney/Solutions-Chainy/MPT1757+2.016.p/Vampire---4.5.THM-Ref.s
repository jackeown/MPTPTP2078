%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 652 expanded)
%              Number of leaves         :   60 ( 329 expanded)
%              Depth                    :   10
%              Number of atoms          : 1484 (6559 expanded)
%              Number of equality atoms :   38 ( 350 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f532,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f114,f118,f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f174,f186,f191,f223,f229,f237,f238,f244,f254,f266,f269,f276,f283,f293,f302,f318,f412,f414,f427,f428,f431,f438,f516,f521])).

fof(f521,plain,
    ( spl8_8
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_19
    | ~ spl8_68 ),
    inference(avatar_split_clause,[],[f520,f514,f189,f352,f349,f136])).

fof(f136,plain,
    ( spl8_8
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f349,plain,
    ( spl8_41
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f352,plain,
    ( spl8_42
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f189,plain,
    ( spl8_19
  <=> m1_subset_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f514,plain,
    ( spl8_68
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(sK7(sK3,sK4),sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f520,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl8_68 ),
    inference(duplicate_literal_removal,[],[f517])).

fof(f517,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl8_68 ),
    inference(resolution,[],[f515,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK7(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK7(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK7(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f515,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK7(sK3,sK4),sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f514])).

fof(f516,plain,
    ( spl8_8
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_19
    | spl8_68
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_55 ),
    inference(avatar_split_clause,[],[f510,f436,f120,f116,f514,f189,f352,f349,f136])).

fof(f116,plain,
    ( spl8_3
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f120,plain,
    ( spl8_4
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f436,plain,
    ( spl8_55
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK3,X2)
        | ~ m1_connsp_2(X1,sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f510,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(sK7(sK3,sK4),sK3,X0)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_55 ),
    inference(resolution,[],[f505,f96])).

fof(f505,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X1,sK3,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK3,X0) )
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_55 ),
    inference(forward_demodulation,[],[f502,f117])).

fof(f117,plain,
    ( sK4 = sK5
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f502,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK3,X0)
        | ~ m1_connsp_2(X1,sK3,sK5) )
    | ~ spl8_4
    | ~ spl8_55 ),
    inference(resolution,[],[f437,f121])).

fof(f121,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f437,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK3,X2)
        | ~ m1_connsp_2(X1,sK3,X0) )
    | ~ spl8_55 ),
    inference(avatar_component_clause,[],[f436])).

fof(f438,plain,
    ( spl8_8
    | ~ spl8_41
    | ~ spl8_42
    | spl8_55
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f432,f355,f436,f352,f349,f136])).

fof(f355,plain,
    ( spl8_43
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(X1,sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f432,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK3,X0)
        | ~ m1_connsp_2(X1,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_43 ),
    inference(resolution,[],[f356,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (20302)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f356,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK3,X0) )
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f355])).

fof(f431,plain,
    ( ~ spl8_13
    | ~ spl8_12
    | ~ spl8_6
    | spl8_41 ),
    inference(avatar_split_clause,[],[f430,f349,f128,f152,f156])).

fof(f156,plain,
    ( spl8_13
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f152,plain,
    ( spl8_12
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f128,plain,
    ( spl8_6
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f430,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_6
    | spl8_41 ),
    inference(resolution,[],[f429,f129])).

fof(f129,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f429,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl8_41 ),
    inference(resolution,[],[f350,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f350,plain,
    ( ~ v2_pre_topc(sK3)
    | spl8_41 ),
    inference(avatar_component_clause,[],[f349])).

fof(f428,plain,
    ( ~ spl8_41
    | ~ spl8_42
    | spl8_43
    | spl8_8
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f345,f316,f136,f355,f352,f349])).

fof(f316,plain,
    ( spl8_34
  <=> ! [X1,X3,X2] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_connsp_2(X2,X1,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f345,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK3,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3) )
    | spl8_8
    | ~ spl8_34 ),
    inference(resolution,[],[f317,f137])).

fof(f137,plain,
    ( ~ v2_struct_0(sK3)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f136])).

fof(f317,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(X1)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_connsp_2(X2,X1,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f316])).

fof(f427,plain,
    ( ~ spl8_12
    | ~ spl8_6
    | spl8_42 ),
    inference(avatar_split_clause,[],[f426,f352,f128,f152])).

fof(f426,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_6
    | spl8_42 ),
    inference(resolution,[],[f415,f129])).

fof(f415,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl8_42 ),
    inference(resolution,[],[f353,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f353,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_42 ),
    inference(avatar_component_clause,[],[f352])).

fof(f414,plain,
    ( spl8_14
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_24
    | ~ spl8_5
    | ~ spl8_25
    | ~ spl8_31
    | spl8_54 ),
    inference(avatar_split_clause,[],[f413,f410,f297,f261,f124,f258,f152,f156,f160])).

fof(f160,plain,
    ( spl8_14
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f258,plain,
    ( spl8_24
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f124,plain,
    ( spl8_5
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f261,plain,
    ( spl8_25
  <=> v3_pre_topc(u1_struct_0(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f297,plain,
    ( spl8_31
  <=> r2_hidden(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f410,plain,
    ( spl8_54
  <=> m1_connsp_2(u1_struct_0(sK3),sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f413,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_54 ),
    inference(resolution,[],[f411,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f411,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | spl8_54 ),
    inference(avatar_component_clause,[],[f410])).

fof(f412,plain,
    ( ~ spl8_54
    | spl8_14
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_5
    | spl8_32 ),
    inference(avatar_split_clause,[],[f408,f300,f124,f152,f156,f160,f410])).

fof(f300,plain,
    ( spl8_32
  <=> r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f408,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | spl8_32 ),
    inference(duplicate_literal_removal,[],[f405])).

fof(f405,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_32 ),
    inference(resolution,[],[f366,f178])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK6(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f81,f95])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK6(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK6(X0,X1,X2),X2)
                & v3_pre_topc(sK6(X0,X1,X2),X0)
                & m1_connsp_2(sK6(X0,X1,X2),X0,X1)
                & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(sK6(X0,X1,X2)) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X3) )
     => ( r1_tarski(sK6(X0,X1,X2),X2)
        & v3_pre_topc(sK6(X0,X1,X2),X0)
        & m1_connsp_2(sK6(X0,X1,X2),X0,X1)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

% (20315)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (20305)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (20319)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (20315)Refutation not found, incomplete strategy% (20315)------------------------------
% (20315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20315)Termination reason: Refutation not found, incomplete strategy

% (20315)Memory used [KB]: 1791
% (20315)Time elapsed: 0.065 s
% (20315)------------------------------
% (20315)------------------------------
fof(f366,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK6(sK1,sK4,u1_struct_0(sK3)),X0,sK4)
        | ~ m1_subset_1(sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl8_32 ),
    inference(resolution,[],[f301,f181])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f84,f95])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f301,plain,
    ( ~ r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | spl8_32 ),
    inference(avatar_component_clause,[],[f300])).

fof(f318,plain,
    ( ~ spl8_19
    | spl8_34
    | spl8_31 ),
    inference(avatar_split_clause,[],[f308,f297,f316,f189])).

fof(f308,plain,
    ( ! [X2,X3,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(X2,X1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3)) )
    | spl8_31 ),
    inference(resolution,[],[f298,f196])).

fof(f196,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ m1_connsp_2(X2,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X4,X3) ) ),
    inference(resolution,[],[f192,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f192,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
      | ~ m1_connsp_2(X0,X1,X2) ) ),
    inference(resolution,[],[f181,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f298,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | spl8_31 ),
    inference(avatar_component_clause,[],[f297])).

fof(f302,plain,
    ( ~ spl8_31
    | ~ spl8_32
    | ~ spl8_5
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f294,f291,f124,f300,f297])).

fof(f291,plain,
    ( spl8_30
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f294,plain,
    ( ~ r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ spl8_5
    | ~ spl8_30 ),
    inference(resolution,[],[f292,f125])).

fof(f125,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))
        | ~ r2_hidden(X0,u1_struct_0(sK3)) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f291])).

fof(f293,plain,
    ( spl8_14
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_24
    | ~ spl8_25
    | spl8_30
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f289,f281,f291,f261,f258,f152,f156,f160])).

fof(f281,plain,
    ( spl8_28
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_28 ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_28 ),
    inference(resolution,[],[f282,f85])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f281])).

fof(f283,plain,
    ( spl8_14
    | ~ spl8_13
    | ~ spl8_12
    | spl8_28
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f279,f264,f281,f152,f156,f160])).

fof(f264,plain,
    ( spl8_26
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_26 ),
    inference(duplicate_literal_removal,[],[f277])).

fof(f277,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_26 ),
    inference(resolution,[],[f265,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f80,f95])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f264])).

fof(f276,plain,
    ( ~ spl8_13
    | ~ spl8_12
    | ~ spl8_24
    | ~ spl8_7
    | ~ spl8_6
    | spl8_25 ),
    inference(avatar_split_clause,[],[f274,f261,f128,f132,f258,f152,f156])).

fof(f132,plain,
    ( spl8_7
  <=> v1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f274,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ v1_tsep_1(sK3,sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl8_25 ),
    inference(resolution,[],[f262,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f262,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | spl8_25 ),
    inference(avatar_component_clause,[],[f261])).

fof(f269,plain,
    ( ~ spl8_12
    | ~ spl8_6
    | spl8_24 ),
    inference(avatar_split_clause,[],[f267,f258,f128,f152])).

fof(f267,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | spl8_24 ),
    inference(resolution,[],[f259,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f259,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl8_24 ),
    inference(avatar_component_clause,[],[f258])).

fof(f266,plain,
    ( spl8_14
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_24
    | ~ spl8_25
    | spl8_26
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f256,f252,f264,f261,f258,f152,f156,f160])).

fof(f252,plain,
    ( spl8_23
  <=> ! [X0] :
        ( ~ m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_23 ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_23 ),
    inference(resolution,[],[f253,f85])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f252])).

fof(f254,plain,
    ( spl8_14
    | ~ spl8_13
    | ~ spl8_12
    | spl8_23
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f250,f235,f252,f152,f156,f160])).

fof(f235,plain,
    ( spl8_22
  <=> ! [X0] :
        ( ~ r2_hidden(sK4,X0)
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_22 ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_22 ),
    inference(resolution,[],[f247,f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f82,f95])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f247,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(sK6(X0,X1,u1_struct_0(sK3)),sK1)
        | ~ m1_subset_1(sK6(X0,X1,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(sK4,sK6(X0,X1,u1_struct_0(sK3)))
        | ~ m1_connsp_2(u1_struct_0(sK3),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_22 ),
    inference(resolution,[],[f236,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK6(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f83,f95])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK6(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ r2_hidden(sK4,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1) )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f235])).

fof(f244,plain,
    ( spl8_17
    | ~ spl8_16
    | ~ spl8_15
    | spl8_14
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_11
    | ~ spl8_10
    | ~ spl8_9
    | spl8_8
    | ~ spl8_6
    | ~ spl8_5
    | ~ spl8_19
    | ~ spl8_1
    | spl8_18 ),
    inference(avatar_split_clause,[],[f240,f184,f106,f189,f124,f128,f136,f140,f144,f148,f152,f156,f160,f164,f168,f172])).

fof(f172,plain,
    ( spl8_17
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f168,plain,
    ( spl8_16
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f164,plain,
    ( spl8_15
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f148,plain,
    ( spl8_11
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f144,plain,
    ( spl8_10
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f140,plain,
    ( spl8_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f106,plain,
    ( spl8_1
  <=> r1_tmap_1(sK1,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f184,plain,
    ( spl8_18
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f240,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_18 ),
    inference(resolution,[],[f231,f98])).

fof(f98,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f231,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f238,plain,
    ( sK4 != sK5
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f237,plain,
    ( ~ spl8_18
    | spl8_8
    | ~ spl8_19
    | spl8_22
    | ~ spl8_6
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f230,f227,f128,f235,f189,f136,f184])).

fof(f227,plain,
    ( spl8_21
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,u1_struct_0(X1))
        | ~ r2_hidden(sK4,X0)
        | ~ v3_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK4,u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(X1,sK1)
        | v2_struct_0(X1)
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,X0)
        | ~ v3_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | v2_struct_0(sK3)
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) )
    | ~ spl8_6
    | ~ spl8_21 ),
    inference(resolution,[],[f228,f129])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK1)
        | ~ r2_hidden(sK4,X0)
        | ~ v3_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK4,u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X0,u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK4) )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( ~ spl8_5
    | spl8_21
    | spl8_1
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f224,f221,f106,f227,f124])).

fof(f221,plain,
    ( spl8_20
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,u1_struct_0(X1))
        | r1_tmap_1(sK1,sK0,sK2,X2)
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ v3_pre_topc(X0,sK1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f224,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(X1))
        | ~ v3_pre_topc(X0,sK1)
        | ~ r2_hidden(sK4,X0) )
    | spl8_1
    | ~ spl8_20 ),
    inference(resolution,[],[f222,f107])).

fof(f107,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f222,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(sK1,sK0,sK2,X2)
        | ~ r1_tarski(X0,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ v3_pre_topc(X0,sK1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f221])).

fof(f223,plain,
    ( spl8_17
    | ~ spl8_16
    | ~ spl8_15
    | spl8_14
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_9
    | spl8_20
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f212,f148,f144,f221,f140,f152,f156,f160,f164,f168,f172])).

fof(f212,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,u1_struct_0(X1))
        | ~ r2_hidden(X2,X0)
        | ~ v3_pre_topc(X0,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(X1,sK1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(resolution,[],[f211,f145])).

fof(f145,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f211,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1))
        | ~ r1_tarski(X4,u1_struct_0(X0))
        | ~ r2_hidden(X3,X4)
        | ~ v3_pre_topc(X4,X2)
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
        | r1_tmap_1(X2,X1,sK2,X3)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_11 ),
    inference(resolution,[],[f99,f149])).

fof(f149,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X6,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | r1_tmap_1(X1,X0,X2,X6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X1,X0,X2,X5)
                                  | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) ) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

% (20321)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f191,plain,
    ( spl8_19
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f187,f120,f116,f189])).

fof(f187,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(superposition,[],[f121,f117])).

fof(f186,plain,
    ( spl8_18
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f182,f116,f109,f184])).

fof(f109,plain,
    ( spl8_2
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f182,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f113,f117])).

fof(f113,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f174,plain,(
    ~ spl8_17 ),
    inference(avatar_split_clause,[],[f60,f172])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
    & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK4) )
    & sK4 = sK5
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_pre_topc(sK3,sK1)
    & v1_tsep_1(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f45,f51,f50,f49,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | r1_tmap_1(X1,X0,X2,X4) )
                            & X4 = X5
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK0,X2,X4) )
                          & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | r1_tmap_1(X1,sK0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,sK0,X2,X4) )
                        & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                          | r1_tmap_1(X1,sK0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_pre_topc(X3,X1)
                & v1_tsep_1(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                        | ~ r1_tmap_1(sK1,sK0,X2,X4) )
                      & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                        | r1_tmap_1(sK1,sK0,X2,X4) )
                      & X4 = X5
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_pre_topc(X3,sK1)
              & v1_tsep_1(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                      | ~ r1_tmap_1(sK1,sK0,X2,X4) )
                    & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                      | r1_tmap_1(sK1,sK0,X2,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_pre_topc(X3,sK1)
            & v1_tsep_1(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                    | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
                  & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                    | r1_tmap_1(sK1,sK0,sK2,X4) )
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_pre_topc(X3,sK1)
          & v1_tsep_1(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                  | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
                & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                  | r1_tmap_1(sK1,sK0,sK2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_pre_topc(X3,sK1)
        & v1_tsep_1(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
                | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
              & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
                | r1_tmap_1(sK1,sK0,sK2,X4) )
              & X4 = X5
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_pre_topc(sK3,sK1)
      & v1_tsep_1(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
              | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
            & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
              | r1_tmap_1(sK1,sK0,sK2,X4) )
            & X4 = X5
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
            | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
          & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
            | r1_tmap_1(sK1,sK0,sK2,sK4) )
          & sK4 = X5
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X5] :
        ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
          | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
        & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
          | r1_tmap_1(sK1,sK0,sK2,sK4) )
        & sK4 = X5
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
        | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
      & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
      & sK4 = sK5
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & v1_tsep_1(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( X4 = X5
                             => ( r1_tmap_1(X1,X0,X2,X4)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f170,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f61,f168])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f166,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f62,f164])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f162,plain,(
    ~ spl8_14 ),
    inference(avatar_split_clause,[],[f63,f160])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f158,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f64,f156])).

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f154,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f65,f152])).

fof(f65,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f150,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f66,f148])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f146,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f67,f144])).

fof(f67,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f142,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f68,f140])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f138,plain,(
    ~ spl8_8 ),
    inference(avatar_split_clause,[],[f69,f136])).

fof(f69,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f134,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f70,f132])).

fof(f70,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f130,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f71,f128])).

fof(f71,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f126,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f72,f124])).

fof(f72,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f122,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f73,f120])).

fof(f73,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f118,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f74,f116])).

fof(f74,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f52])).

fof(f114,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f75,f109,f106])).

fof(f75,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f111,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f76,f109,f106])).

fof(f76,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:39:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (20316)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (20304)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (20308)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (20306)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (20307)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (20308)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f532,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f111,f114,f118,f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f174,f186,f191,f223,f229,f237,f238,f244,f254,f266,f269,f276,f283,f293,f302,f318,f412,f414,f427,f428,f431,f438,f516,f521])).
% 0.21/0.48  fof(f521,plain,(
% 0.21/0.48    spl8_8 | ~spl8_41 | ~spl8_42 | ~spl8_19 | ~spl8_68),
% 0.21/0.48    inference(avatar_split_clause,[],[f520,f514,f189,f352,f349,f136])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl8_8 <=> v2_struct_0(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.48  fof(f349,plain,(
% 0.21/0.48    spl8_41 <=> v2_pre_topc(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 0.21/0.48  fof(f352,plain,(
% 0.21/0.48    spl8_42 <=> l1_pre_topc(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    spl8_19 <=> m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.48  fof(f514,plain,(
% 0.21/0.48    spl8_68 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_connsp_2(sK7(sK3,sK4),sK3,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).
% 0.21/0.48  fof(f520,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl8_68),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f517])).
% 0.21/0.48  fof(f517,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl8_68),
% 0.21/0.48    inference(resolution,[],[f515,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_connsp_2(sK7(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_connsp_2(sK7(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK7(X0,X1),X0,X1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.21/0.48  fof(f515,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_connsp_2(sK7(sK3,sK4),sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | ~spl8_68),
% 0.21/0.48    inference(avatar_component_clause,[],[f514])).
% 0.21/0.48  fof(f516,plain,(
% 0.21/0.48    spl8_8 | ~spl8_41 | ~spl8_42 | ~spl8_19 | spl8_68 | ~spl8_3 | ~spl8_4 | ~spl8_55),
% 0.21/0.48    inference(avatar_split_clause,[],[f510,f436,f120,f116,f514,f189,f352,f349,f136])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl8_3 <=> sK4 = sK5),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl8_4 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.48  fof(f436,plain,(
% 0.21/0.48    spl8_55 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK3,X2) | ~m1_connsp_2(X1,sK3,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).
% 0.21/0.48  fof(f510,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_connsp_2(sK7(sK3,sK4),sK3,X0) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | (~spl8_3 | ~spl8_4 | ~spl8_55)),
% 0.21/0.48    inference(resolution,[],[f505,f96])).
% 0.21/0.48  fof(f505,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_connsp_2(X1,sK3,sK4) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK3,X0)) ) | (~spl8_3 | ~spl8_4 | ~spl8_55)),
% 0.21/0.48    inference(forward_demodulation,[],[f502,f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    sK4 = sK5 | ~spl8_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f116])).
% 0.21/0.48  fof(f502,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK3,X0) | ~m1_connsp_2(X1,sK3,sK5)) ) | (~spl8_4 | ~spl8_55)),
% 0.21/0.48    inference(resolution,[],[f437,f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl8_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f120])).
% 0.21/0.48  fof(f437,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK3,X2) | ~m1_connsp_2(X1,sK3,X0)) ) | ~spl8_55),
% 0.21/0.48    inference(avatar_component_clause,[],[f436])).
% 0.21/0.48  fof(f438,plain,(
% 0.21/0.48    spl8_8 | ~spl8_41 | ~spl8_42 | spl8_55 | ~spl8_43),
% 0.21/0.48    inference(avatar_split_clause,[],[f432,f355,f436,f352,f349,f136])).
% 0.21/0.48  fof(f355,plain,(
% 0.21/0.48    spl8_43 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(X1,sK3,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 0.21/0.48  fof(f432,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK3,X0) | ~m1_connsp_2(X1,sK3,X2) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_43),
% 0.21/0.48    inference(resolution,[],[f356,f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  % (20302)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK3,X0)) ) | ~spl8_43),
% 0.21/0.48    inference(avatar_component_clause,[],[f355])).
% 0.21/0.48  fof(f431,plain,(
% 0.21/0.48    ~spl8_13 | ~spl8_12 | ~spl8_6 | spl8_41),
% 0.21/0.48    inference(avatar_split_clause,[],[f430,f349,f128,f152,f156])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl8_13 <=> v2_pre_topc(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl8_12 <=> l1_pre_topc(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl8_6 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.48  fof(f430,plain,(
% 0.21/0.48    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_6 | spl8_41)),
% 0.21/0.48    inference(resolution,[],[f429,f129])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    m1_pre_topc(sK3,sK1) | ~spl8_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f128])).
% 0.21/0.48  fof(f429,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl8_41),
% 0.21/0.48    inference(resolution,[],[f350,f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.48  fof(f350,plain,(
% 0.21/0.48    ~v2_pre_topc(sK3) | spl8_41),
% 0.21/0.48    inference(avatar_component_clause,[],[f349])).
% 0.21/0.48  fof(f428,plain,(
% 0.21/0.48    ~spl8_41 | ~spl8_42 | spl8_43 | spl8_8 | ~spl8_34),
% 0.21/0.48    inference(avatar_split_clause,[],[f345,f316,f136,f355,f352,f349])).
% 0.21/0.48  fof(f316,plain,(
% 0.21/0.48    spl8_34 <=> ! [X1,X3,X2] : (~l1_pre_topc(X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_connsp_2(X2,X1,X3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(X1) | ~v2_pre_topc(X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK3,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)) ) | (spl8_8 | ~spl8_34)),
% 0.21/0.48    inference(resolution,[],[f317,f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ~v2_struct_0(sK3) | spl8_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f136])).
% 0.21/0.48  fof(f317,plain,(
% 0.21/0.48    ( ! [X2,X3,X1] : (v2_struct_0(X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_connsp_2(X2,X1,X3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | ~spl8_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f316])).
% 0.21/0.48  fof(f427,plain,(
% 0.21/0.48    ~spl8_12 | ~spl8_6 | spl8_42),
% 0.21/0.48    inference(avatar_split_clause,[],[f426,f352,f128,f152])).
% 0.21/0.48  fof(f426,plain,(
% 0.21/0.48    ~l1_pre_topc(sK1) | (~spl8_6 | spl8_42)),
% 0.21/0.48    inference(resolution,[],[f415,f129])).
% 0.21/0.48  fof(f415,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl8_42),
% 0.21/0.48    inference(resolution,[],[f353,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f353,plain,(
% 0.21/0.48    ~l1_pre_topc(sK3) | spl8_42),
% 0.21/0.48    inference(avatar_component_clause,[],[f352])).
% 0.21/0.48  fof(f414,plain,(
% 0.21/0.48    spl8_14 | ~spl8_13 | ~spl8_12 | ~spl8_24 | ~spl8_5 | ~spl8_25 | ~spl8_31 | spl8_54),
% 0.21/0.48    inference(avatar_split_clause,[],[f413,f410,f297,f261,f124,f258,f152,f156,f160])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    spl8_14 <=> v2_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    spl8_24 <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl8_5 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    spl8_25 <=> v3_pre_topc(u1_struct_0(sK3),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    spl8_31 <=> r2_hidden(sK4,u1_struct_0(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.48  fof(f410,plain,(
% 0.21/0.48    spl8_54 <=> m1_connsp_2(u1_struct_0(sK3),sK1,sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).
% 0.21/0.48  fof(f413,plain,(
% 0.21/0.48    ~r2_hidden(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_54),
% 0.21/0.48    inference(resolution,[],[f411,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.48  fof(f411,plain,(
% 0.21/0.48    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | spl8_54),
% 0.21/0.48    inference(avatar_component_clause,[],[f410])).
% 0.21/0.48  fof(f412,plain,(
% 0.21/0.48    ~spl8_54 | spl8_14 | ~spl8_13 | ~spl8_12 | ~spl8_5 | spl8_32),
% 0.21/0.48    inference(avatar_split_clause,[],[f408,f300,f124,f152,f156,f160,f410])).
% 0.21/0.48  fof(f300,plain,(
% 0.21/0.48    spl8_32 <=> r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.48  fof(f408,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | spl8_32),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f405])).
% 0.21/0.48  fof(f405,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_32),
% 0.21/0.48    inference(resolution,[],[f366,f178])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_connsp_2(sK6(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f95])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_connsp_2(sK6(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK6(X0,X1,X2),X2) & v3_pre_topc(sK6(X0,X1,X2),X0) & m1_connsp_2(sK6(X0,X1,X2),X0,X1) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK6(X0,X1,X2))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => (r1_tarski(sK6(X0,X1,X2),X2) & v3_pre_topc(sK6(X0,X1,X2),X0) & m1_connsp_2(sK6(X0,X1,X2),X0,X1) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK6(X0,X1,X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.21/0.48  % (20315)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (20305)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (20319)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (20315)Refutation not found, incomplete strategy% (20315)------------------------------
% 0.21/0.49  % (20315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20315)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (20315)Memory used [KB]: 1791
% 0.21/0.49  % (20315)Time elapsed: 0.065 s
% 0.21/0.49  % (20315)------------------------------
% 0.21/0.49  % (20315)------------------------------
% 0.21/0.49  fof(f366,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_connsp_2(sK6(sK1,sK4,u1_struct_0(sK3)),X0,sK4) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | spl8_32),
% 0.21/0.49    inference(resolution,[],[f301,f181])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f84,f95])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    ~r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | spl8_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f300])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    ~spl8_19 | spl8_34 | spl8_31),
% 0.21/0.49    inference(avatar_split_clause,[],[f308,f297,f316,f189])).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    ( ! [X2,X3,X1] : (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(X2,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(sK4,u1_struct_0(sK3))) ) | spl8_31),
% 0.21/0.49    inference(resolution,[],[f298,f196])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X4,X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~m1_connsp_2(X2,X1,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X4,X3)) )),
% 0.21/0.49    inference(resolution,[],[f192,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_xboole_0(X3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(X3)) | ~m1_connsp_2(X0,X1,X2)) )),
% 0.21/0.49    inference(resolution,[],[f181,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    ~r2_hidden(sK4,u1_struct_0(sK3)) | spl8_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f297])).
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    ~spl8_31 | ~spl8_32 | ~spl8_5 | ~spl8_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f294,f291,f124,f300,f297])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    spl8_30 <=> ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) | ~m1_subset_1(X0,u1_struct_0(sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    ~r2_hidden(sK4,sK6(sK1,sK4,u1_struct_0(sK3))) | ~r2_hidden(sK4,u1_struct_0(sK3)) | (~spl8_5 | ~spl8_30)),
% 0.21/0.49    inference(resolution,[],[f292,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    m1_subset_1(sK4,u1_struct_0(sK1)) | ~spl8_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f124])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) | ~r2_hidden(X0,u1_struct_0(sK3))) ) | ~spl8_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f291])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    spl8_14 | ~spl8_13 | ~spl8_12 | ~spl8_24 | ~spl8_25 | spl8_30 | ~spl8_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f289,f281,f291,f261,f258,f152,f156,f160])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    spl8_28 <=> ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl8_28),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f288])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl8_28),
% 0.21/0.49    inference(resolution,[],[f282,f85])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))) ) | ~spl8_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f281])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    spl8_14 | ~spl8_13 | ~spl8_12 | spl8_28 | ~spl8_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f279,f264,f281,f152,f156,f160])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    spl8_26 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) | ~m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl8_26),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f277])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl8_26),
% 0.21/0.49    inference(resolution,[],[f265,f177])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f80,f95])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f54])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl8_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f264])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    ~spl8_13 | ~spl8_12 | ~spl8_24 | ~spl8_7 | ~spl8_6 | spl8_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f274,f261,f128,f132,f258,f152,f156])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl8_7 <=> v1_tsep_1(sK3,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    ~m1_pre_topc(sK3,sK1) | ~v1_tsep_1(sK3,sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl8_25),
% 0.21/0.49    inference(resolution,[],[f262,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    ~v3_pre_topc(u1_struct_0(sK3),sK1) | spl8_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f261])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ~spl8_12 | ~spl8_6 | spl8_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f267,f258,f128,f152])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ~m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | spl8_24),
% 0.21/0.49    inference(resolution,[],[f259,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl8_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f258])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    spl8_14 | ~spl8_13 | ~spl8_12 | ~spl8_24 | ~spl8_25 | spl8_26 | ~spl8_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f256,f252,f264,f261,f258,f152,f156,f160])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    spl8_23 <=> ! [X0] : (~m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl8_23),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f255])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl8_23),
% 0.21/0.49    inference(resolution,[],[f253,f85])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3)))) ) | ~spl8_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f252])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    spl8_14 | ~spl8_13 | ~spl8_12 | spl8_23 | ~spl8_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f250,f235,f252,f152,f156,f160])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    spl8_22 <=> ! [X0] : (~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl8_22),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f249])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK6(sK1,X0,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,sK6(sK1,X0,u1_struct_0(sK3))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl8_22),
% 0.21/0.49    inference(resolution,[],[f247,f179])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v3_pre_topc(sK6(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f82,f95])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v3_pre_topc(sK6(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f54])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_pre_topc(sK6(X0,X1,u1_struct_0(sK3)),sK1) | ~m1_subset_1(sK6(X0,X1,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,sK6(X0,X1,u1_struct_0(sK3))) | ~m1_connsp_2(u1_struct_0(sK3),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl8_22),
% 0.21/0.49    inference(resolution,[],[f236,f180])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(sK6(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f83,f95])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(sK6(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f54])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~r2_hidden(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1)) ) | ~spl8_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f235])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    spl8_17 | ~spl8_16 | ~spl8_15 | spl8_14 | ~spl8_13 | ~spl8_12 | ~spl8_11 | ~spl8_10 | ~spl8_9 | spl8_8 | ~spl8_6 | ~spl8_5 | ~spl8_19 | ~spl8_1 | spl8_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f240,f184,f106,f189,f124,f128,f136,f140,f144,f148,f152,f156,f160,f164,f168,f172])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    spl8_17 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    spl8_16 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl8_15 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl8_11 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl8_10 <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl8_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl8_1 <=> r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    spl8_18 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_18),
% 0.21/0.49    inference(resolution,[],[f231,f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | spl8_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f184])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    sK4 != sK5 | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ~spl8_18 | spl8_8 | ~spl8_19 | spl8_22 | ~spl8_6 | ~spl8_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f230,f227,f128,f235,f189,f136,f184])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    spl8_21 <=> ! [X1,X0] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r2_hidden(sK4,X0) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK4,X0) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | v2_struct_0(sK3) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)) ) | (~spl8_6 | ~spl8_21)),
% 0.21/0.49    inference(resolution,[],[f228,f129])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,sK1) | ~r2_hidden(sK4,X0) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK4)) ) | ~spl8_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f227])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    ~spl8_5 | spl8_21 | spl8_1 | ~spl8_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f224,f221,f106,f227,f124])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    spl8_20 <=> ! [X1,X0,X2] : (~r1_tarski(X0,u1_struct_0(X1)) | r1_tmap_1(sK1,sK0,sK2,X2) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(X2,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK4) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(X1)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0)) ) | (spl8_1 | ~spl8_20)),
% 0.21/0.49    inference(resolution,[],[f222,f107])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ~r1_tmap_1(sK1,sK0,sK2,sK4) | spl8_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f106])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tmap_1(sK1,sK0,sK2,X2) | ~r1_tarski(X0,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v3_pre_topc(X0,sK1) | ~r2_hidden(X2,X0)) ) | ~spl8_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f221])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    spl8_17 | ~spl8_16 | ~spl8_15 | spl8_14 | ~spl8_13 | ~spl8_12 | ~spl8_9 | spl8_20 | ~spl8_10 | ~spl8_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f212,f148,f144,f221,f140,f152,f156,f160,f164,f168,f172])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r2_hidden(X2,X0) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_10 | ~spl8_11)),
% 0.21/0.49    inference(resolution,[],[f211,f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl8_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f144])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1)) | ~r1_tarski(X4,u1_struct_0(X0)) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3) | r1_tmap_1(X2,X1,sK2,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl8_11),
% 0.21/0.49    inference(resolution,[],[f99,f149])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    v1_funct_1(sK2) | ~spl8_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | r1_tmap_1(X1,X0,X2,X6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f30])).
% 0.21/0.49  % (20321)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl8_19 | ~spl8_3 | ~spl8_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f187,f120,f116,f189])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl8_3 | ~spl8_4)),
% 0.21/0.49    inference(superposition,[],[f121,f117])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    spl8_18 | ~spl8_2 | ~spl8_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f182,f116,f109,f184])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl8_2 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | (~spl8_2 | ~spl8_3)),
% 0.21/0.49    inference(forward_demodulation,[],[f113,f117])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~spl8_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f109])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ~spl8_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f172])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f45,f51,f50,f49,f48,f47,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | ~r1_tmap_1(sK1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | r1_tmap_1(sK1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | ~r1_tmap_1(sK1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | r1_tmap_1(sK1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ? [X4] : (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(sK1))) => (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) => ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f15])).
% 0.21/0.49  fof(f15,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl8_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f61,f168])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    spl8_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f62,f164])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ~spl8_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f63,f160])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~v2_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    spl8_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f64,f156])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    v2_pre_topc(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl8_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f65,f152])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    l1_pre_topc(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl8_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f66,f148])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl8_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f67,f144])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    spl8_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f68,f140])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ~spl8_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f69,f136])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~v2_struct_0(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl8_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f70,f132])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    v1_tsep_1(sK3,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl8_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f71,f128])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    m1_pre_topc(sK3,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl8_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f72,f124])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl8_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f73,f120])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl8_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f74,f116])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    sK4 = sK5),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl8_1 | spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f75,f109,f106])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~spl8_1 | ~spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f76,f109,f106])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (20308)------------------------------
% 0.21/0.49  % (20308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20308)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (20308)Memory used [KB]: 11129
% 0.21/0.49  % (20308)Time elapsed: 0.067 s
% 0.21/0.49  % (20308)------------------------------
% 0.21/0.49  % (20308)------------------------------
% 0.21/0.49  % (20311)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (20303)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (20300)Success in time 0.132 s
%------------------------------------------------------------------------------
