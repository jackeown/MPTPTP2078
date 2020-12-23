%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 297 expanded)
%              Number of leaves         :   43 ( 139 expanded)
%              Depth                    :   10
%              Number of atoms          :  561 (1263 expanded)
%              Number of equality atoms :  118 ( 297 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f441,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f98,f111,f117,f120,f132,f138,f154,f164,f206,f220,f227,f231,f232,f247,f272,f277,f310,f318,f319,f328,f355,f439])).

fof(f439,plain,
    ( ~ spl8_43
    | ~ spl8_5
    | ~ spl8_29
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f437,f245,f229,f86,f353])).

fof(f353,plain,
    ( spl8_43
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f86,plain,
    ( spl8_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f229,plain,
    ( spl8_29
  <=> r2_hidden(sK4,k7_relset_1(sK0,k1_xboole_0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f245,plain,
    ( spl8_31
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f437,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_5
    | ~ spl8_29
    | ~ spl8_31 ),
    inference(forward_demodulation,[],[f435,f246])).

fof(f246,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f245])).

fof(f435,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_5
    | ~ spl8_29 ),
    inference(resolution,[],[f230,f90])).

fof(f90,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X2,k7_relset_1(X1,k1_xboole_0,X0,X3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) )
    | ~ spl8_5 ),
    inference(resolution,[],[f57,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f56,f87])).

fof(f87,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f230,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,k1_xboole_0,sK3,sK2))
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f229])).

fof(f355,plain,
    ( spl8_43
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f351,f245,f201,f74,f353])).

fof(f74,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f201,plain,
    ( spl8_24
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f351,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_31 ),
    inference(forward_demodulation,[],[f331,f202])).

fof(f202,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f201])).

fof(f331,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_2
    | ~ spl8_31 ),
    inference(superposition,[],[f75,f246])).

fof(f75,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f328,plain,
    ( spl8_26
    | ~ spl8_2
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f236,f201,f74,f214])).

fof(f214,plain,
    ( spl8_26
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f236,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_2
    | ~ spl8_24 ),
    inference(superposition,[],[f75,f202])).

fof(f319,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | k1_xboole_0 != sK0
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f318,plain,
    ( ~ spl8_36
    | spl8_39
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f311,f306,f316,f275])).

fof(f275,plain,
    ( spl8_36
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f316,plain,
    ( spl8_39
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f306,plain,
    ( spl8_38
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f311,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_38 ),
    inference(resolution,[],[f307,f68])).

fof(f68,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f307,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f306])).

fof(f310,plain,
    ( spl8_38
    | ~ spl8_27
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f300,f242,f218,f306])).

fof(f218,plain,
    ( spl8_27
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f242,plain,
    ( spl8_30
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f300,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_27
    | ~ spl8_30 ),
    inference(superposition,[],[f219,f243])).

fof(f243,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f242])).

fof(f219,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f218])).

fof(f277,plain,
    ( spl8_36
    | ~ spl8_26
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f273,f242,f214,f275])).

fof(f273,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_26
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f215,f243])).

fof(f215,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f214])).

fof(f272,plain,
    ( ~ spl8_6
    | ~ spl8_9
    | spl8_15 ),
    inference(avatar_split_clause,[],[f271,f152,f109,f96])).

fof(f96,plain,
    ( spl8_6
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f109,plain,
    ( spl8_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK7(sK3,X1,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f152,plain,
    ( spl8_15
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f271,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_9
    | spl8_15 ),
    inference(resolution,[],[f153,f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(sK3,X1,X0),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f153,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | spl8_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f247,plain,
    ( ~ spl8_26
    | spl8_30
    | spl8_31
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f238,f218,f245,f242,f214])).

fof(f238,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_27 ),
    inference(resolution,[],[f219,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f232,plain,
    ( sK0 != k1_relat_1(sK3)
    | r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f231,plain,
    ( spl8_29
    | ~ spl8_1
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f209,f201,f70,f229])).

fof(f70,plain,
    ( spl8_1
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f209,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,k1_xboole_0,sK3,sK2))
    | ~ spl8_1
    | ~ spl8_24 ),
    inference(superposition,[],[f71,f202])).

fof(f71,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f227,plain,
    ( ~ spl8_2
    | spl8_28
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f222,f204,f224,f74])).

fof(f224,plain,
    ( spl8_28
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f204,plain,
    ( spl8_25
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f222,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_25 ),
    inference(superposition,[],[f49,f205])).

fof(f205,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f204])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f220,plain,
    ( spl8_27
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f211,f201,f78,f218])).

fof(f78,plain,
    ( spl8_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f211,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(superposition,[],[f79,f202])).

fof(f79,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f206,plain,
    ( ~ spl8_2
    | spl8_24
    | spl8_25
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f199,f78,f204,f201,f74])).

fof(f199,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(resolution,[],[f50,f79])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f164,plain,
    ( ~ spl8_8
    | ~ spl8_4
    | ~ spl8_6
    | spl8_16 ),
    inference(avatar_split_clause,[],[f162,f156,f96,f82,f106])).

fof(f106,plain,
    ( spl8_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f82,plain,
    ( spl8_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f156,plain,
    ( spl8_16
  <=> r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f162,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl8_16 ),
    inference(resolution,[],[f157,f63])).

fof(f63,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
                  & r2_hidden(sK6(X0,X1,X2),X1)
                  & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
                    & r2_hidden(sK7(X0,X1,X6),X1)
                    & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f27,f30,f29,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
        & r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f157,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))
    | spl8_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f154,plain,
    ( ~ spl8_14
    | ~ spl8_15
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f147,f136,f152,f149])).

fof(f149,plain,
    ( spl8_14
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f136,plain,
    ( spl8_12
  <=> sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f147,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_12 ),
    inference(trivial_inequality_removal,[],[f145])).

fof(f145,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_12 ),
    inference(superposition,[],[f37,f137])).

fof(f137,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f37,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ r2_hidden(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(f138,plain,
    ( spl8_12
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f133,f130,f96,f136])).

fof(f130,plain,
    ( spl8_11
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f133,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(resolution,[],[f131,f97])).

fof(f97,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( ~ spl8_8
    | spl8_11
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f128,f82,f130,f106])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl8_4 ),
    inference(resolution,[],[f61,f83])).

fof(f83,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f61,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f120,plain,(
    spl8_10 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl8_10 ),
    inference(resolution,[],[f116,f48])).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f116,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_10
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f117,plain,
    ( ~ spl8_10
    | ~ spl8_2
    | spl8_8 ),
    inference(avatar_split_clause,[],[f113,f106,f74,f115])).

fof(f113,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_2
    | spl8_8 ),
    inference(resolution,[],[f112,f75])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl8_8 ),
    inference(resolution,[],[f107,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f107,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f111,plain,
    ( ~ spl8_8
    | spl8_9
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f104,f82,f109,f106])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK7(sK3,X1,X0),X1)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_4 ),
    inference(resolution,[],[f62,f83])).

fof(f62,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(sK7(X0,X1,X6),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,
    ( spl8_6
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f93,f74,f70,f96])).

fof(f93,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(superposition,[],[f71,f91])).

fof(f91,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl8_2 ),
    inference(resolution,[],[f58,f75])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f88,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f38,f86])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f84,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f33,f82])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f36,f70])).

fof(f36,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:01:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (10870)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.45  % (10870)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f441,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f98,f111,f117,f120,f132,f138,f154,f164,f206,f220,f227,f231,f232,f247,f272,f277,f310,f318,f319,f328,f355,f439])).
% 0.21/0.46  fof(f439,plain,(
% 0.21/0.46    ~spl8_43 | ~spl8_5 | ~spl8_29 | ~spl8_31),
% 0.21/0.46    inference(avatar_split_clause,[],[f437,f245,f229,f86,f353])).
% 0.21/0.46  fof(f353,plain,(
% 0.21/0.46    spl8_43 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    spl8_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.46  fof(f229,plain,(
% 0.21/0.46    spl8_29 <=> r2_hidden(sK4,k7_relset_1(sK0,k1_xboole_0,sK3,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.21/0.46  fof(f245,plain,(
% 0.21/0.46    spl8_31 <=> k1_xboole_0 = sK3),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.46  fof(f437,plain,(
% 0.21/0.46    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_5 | ~spl8_29 | ~spl8_31)),
% 0.21/0.46    inference(forward_demodulation,[],[f435,f246])).
% 0.21/0.46  fof(f246,plain,(
% 0.21/0.46    k1_xboole_0 = sK3 | ~spl8_31),
% 0.21/0.46    inference(avatar_component_clause,[],[f245])).
% 0.21/0.46  fof(f435,plain,(
% 0.21/0.46    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_5 | ~spl8_29)),
% 0.21/0.46    inference(resolution,[],[f230,f90])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,k7_relset_1(X1,k1_xboole_0,X0,X3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))) ) | ~spl8_5),
% 0.21/0.46    inference(resolution,[],[f57,f89])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl8_5),
% 0.21/0.46    inference(resolution,[],[f56,f87])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0) | ~spl8_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f86])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.21/0.46  fof(f230,plain,(
% 0.21/0.46    r2_hidden(sK4,k7_relset_1(sK0,k1_xboole_0,sK3,sK2)) | ~spl8_29),
% 0.21/0.46    inference(avatar_component_clause,[],[f229])).
% 0.21/0.46  fof(f355,plain,(
% 0.21/0.46    spl8_43 | ~spl8_2 | ~spl8_24 | ~spl8_31),
% 0.21/0.46    inference(avatar_split_clause,[],[f351,f245,f201,f74,f353])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    spl8_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.46  fof(f201,plain,(
% 0.21/0.46    spl8_24 <=> k1_xboole_0 = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.46  fof(f351,plain,(
% 0.21/0.46    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_2 | ~spl8_24 | ~spl8_31)),
% 0.21/0.46    inference(forward_demodulation,[],[f331,f202])).
% 0.21/0.46  fof(f202,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | ~spl8_24),
% 0.21/0.46    inference(avatar_component_clause,[],[f201])).
% 0.21/0.46  fof(f331,plain,(
% 0.21/0.46    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl8_2 | ~spl8_31)),
% 0.21/0.46    inference(superposition,[],[f75,f246])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f74])).
% 0.21/0.46  fof(f328,plain,(
% 0.21/0.46    spl8_26 | ~spl8_2 | ~spl8_24),
% 0.21/0.46    inference(avatar_split_clause,[],[f236,f201,f74,f214])).
% 0.21/0.46  fof(f214,plain,(
% 0.21/0.46    spl8_26 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.46  fof(f236,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_2 | ~spl8_24)),
% 0.21/0.46    inference(superposition,[],[f75,f202])).
% 0.21/0.46  fof(f319,plain,(
% 0.21/0.46    k1_xboole_0 != sK1 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | k1_xboole_0 != sK0 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.46  fof(f318,plain,(
% 0.21/0.46    ~spl8_36 | spl8_39 | ~spl8_38),
% 0.21/0.46    inference(avatar_split_clause,[],[f311,f306,f316,f275])).
% 0.21/0.46  fof(f275,plain,(
% 0.21/0.46    spl8_36 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.21/0.46  fof(f316,plain,(
% 0.21/0.46    spl8_39 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.21/0.46  fof(f306,plain,(
% 0.21/0.46    spl8_38 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.21/0.46  fof(f311,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl8_38),
% 0.21/0.46    inference(resolution,[],[f307,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.46    inference(equality_resolution,[],[f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(nnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(flattening,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.46  fof(f307,plain,(
% 0.21/0.46    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl8_38),
% 0.21/0.46    inference(avatar_component_clause,[],[f306])).
% 0.21/0.46  fof(f310,plain,(
% 0.21/0.46    spl8_38 | ~spl8_27 | ~spl8_30),
% 0.21/0.46    inference(avatar_split_clause,[],[f300,f242,f218,f306])).
% 0.21/0.46  fof(f218,plain,(
% 0.21/0.46    spl8_27 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.46  fof(f242,plain,(
% 0.21/0.46    spl8_30 <=> k1_xboole_0 = sK0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.46  fof(f300,plain,(
% 0.21/0.46    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl8_27 | ~spl8_30)),
% 0.21/0.46    inference(superposition,[],[f219,f243])).
% 0.21/0.46  fof(f243,plain,(
% 0.21/0.46    k1_xboole_0 = sK0 | ~spl8_30),
% 0.21/0.46    inference(avatar_component_clause,[],[f242])).
% 0.21/0.46  fof(f219,plain,(
% 0.21/0.46    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl8_27),
% 0.21/0.46    inference(avatar_component_clause,[],[f218])).
% 0.21/0.46  fof(f277,plain,(
% 0.21/0.46    spl8_36 | ~spl8_26 | ~spl8_30),
% 0.21/0.46    inference(avatar_split_clause,[],[f273,f242,f214,f275])).
% 0.21/0.46  fof(f273,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_26 | ~spl8_30)),
% 0.21/0.46    inference(forward_demodulation,[],[f215,f243])).
% 0.21/0.46  fof(f215,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_26),
% 0.21/0.46    inference(avatar_component_clause,[],[f214])).
% 0.21/0.46  fof(f272,plain,(
% 0.21/0.46    ~spl8_6 | ~spl8_9 | spl8_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f271,f152,f109,f96])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    spl8_6 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    spl8_9 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK7(sK3,X1,X0),X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    spl8_15 <=> r2_hidden(sK7(sK3,sK2,sK4),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.46  fof(f271,plain,(
% 0.21/0.46    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_9 | spl8_15)),
% 0.21/0.46    inference(resolution,[],[f153,f110])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(sK7(sK3,X1,X0),X1) | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl8_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f109])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    ~r2_hidden(sK7(sK3,sK2,sK4),sK2) | spl8_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f152])).
% 0.21/0.46  fof(f247,plain,(
% 0.21/0.46    ~spl8_26 | spl8_30 | spl8_31 | ~spl8_27),
% 0.21/0.46    inference(avatar_split_clause,[],[f238,f218,f245,f242,f214])).
% 0.21/0.46  fof(f238,plain,(
% 0.21/0.46    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_27),
% 0.21/0.46    inference(resolution,[],[f219,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.46    inference(equality_resolution,[],[f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f32])).
% 0.21/0.46  fof(f232,plain,(
% 0.21/0.46    sK0 != k1_relat_1(sK3) | r2_hidden(sK7(sK3,sK2,sK4),sK0) | ~r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))),
% 0.21/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.46  fof(f231,plain,(
% 0.21/0.46    spl8_29 | ~spl8_1 | ~spl8_24),
% 0.21/0.46    inference(avatar_split_clause,[],[f209,f201,f70,f229])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    spl8_1 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.46  fof(f209,plain,(
% 0.21/0.46    r2_hidden(sK4,k7_relset_1(sK0,k1_xboole_0,sK3,sK2)) | (~spl8_1 | ~spl8_24)),
% 0.21/0.46    inference(superposition,[],[f71,f202])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f70])).
% 0.21/0.46  fof(f227,plain,(
% 0.21/0.46    ~spl8_2 | spl8_28 | ~spl8_25),
% 0.21/0.46    inference(avatar_split_clause,[],[f222,f204,f224,f74])).
% 0.21/0.46  fof(f224,plain,(
% 0.21/0.46    spl8_28 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.46  fof(f204,plain,(
% 0.21/0.46    spl8_25 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.46  fof(f222,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_25),
% 0.21/0.46    inference(superposition,[],[f49,f205])).
% 0.21/0.46  fof(f205,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl8_25),
% 0.21/0.46    inference(avatar_component_clause,[],[f204])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.46  fof(f220,plain,(
% 0.21/0.46    spl8_27 | ~spl8_3 | ~spl8_24),
% 0.21/0.46    inference(avatar_split_clause,[],[f211,f201,f78,f218])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl8_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.46  fof(f211,plain,(
% 0.21/0.46    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl8_3 | ~spl8_24)),
% 0.21/0.46    inference(superposition,[],[f79,f202])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    v1_funct_2(sK3,sK0,sK1) | ~spl8_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f78])).
% 0.21/0.46  fof(f206,plain,(
% 0.21/0.46    ~spl8_2 | spl8_24 | spl8_25 | ~spl8_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f199,f78,f204,f201,f74])).
% 0.21/0.46  fof(f199,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_3),
% 0.21/0.46    inference(resolution,[],[f50,f79])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f32])).
% 0.21/0.46  fof(f164,plain,(
% 0.21/0.46    ~spl8_8 | ~spl8_4 | ~spl8_6 | spl8_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f162,f156,f96,f82,f106])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    spl8_8 <=> v1_relat_1(sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    spl8_4 <=> v1_funct_1(sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.46  fof(f156,plain,(
% 0.21/0.46    spl8_16 <=> r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl8_16),
% 0.21/0.46    inference(resolution,[],[f157,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X6,X0,X1] : (r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X6,X2,X0,X1] : (r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f27,f30,f29,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(rectify,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.46  fof(f157,plain,(
% 0.21/0.46    ~r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) | spl8_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f156])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    ~spl8_14 | ~spl8_15 | ~spl8_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f147,f136,f152,f149])).
% 0.21/0.46  fof(f149,plain,(
% 0.21/0.46    spl8_14 <=> r2_hidden(sK7(sK3,sK2,sK4),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    spl8_12 <=> sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    ~r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~r2_hidden(sK7(sK3,sK2,sK4),sK0) | ~spl8_12),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f145])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    sK4 != sK4 | ~r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~r2_hidden(sK7(sK3,sK2,sK4),sK0) | ~spl8_12),
% 0.21/0.46    inference(superposition,[],[f37,f137])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~spl8_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f136])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f24,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.46    inference(negated_conjecture,[],[f10])).
% 0.21/0.46  fof(f10,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    spl8_12 | ~spl8_6 | ~spl8_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f133,f130,f96,f136])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    spl8_11 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | (~spl8_6 | ~spl8_11)),
% 0.21/0.46    inference(resolution,[],[f131,f97])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl8_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f96])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0) ) | ~spl8_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f130])).
% 0.21/0.46  fof(f132,plain,(
% 0.21/0.46    ~spl8_8 | spl8_11 | ~spl8_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f128,f82,f130,f106])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl8_4),
% 0.21/0.46    inference(resolution,[],[f61,f83])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    v1_funct_1(sK3) | ~spl8_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f82])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X6,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | k1_funct_1(X0,sK7(X0,X1,X6)) = X6 | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    spl8_10),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    $false | spl8_10),
% 0.21/0.46    inference(resolution,[],[f116,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl8_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f115])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    spl8_10 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    ~spl8_10 | ~spl8_2 | spl8_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f113,f106,f74,f115])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl8_2 | spl8_8)),
% 0.21/0.46    inference(resolution,[],[f112,f75])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl8_8),
% 0.21/0.46    inference(resolution,[],[f107,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    ~v1_relat_1(sK3) | spl8_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f106])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    ~spl8_8 | spl8_9 | ~spl8_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f104,f82,f109,f106])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK7(sK3,X1,X0),X1) | ~v1_relat_1(sK3)) ) | ~spl8_4),
% 0.21/0.46    inference(resolution,[],[f62,f83])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X6,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | r2_hidden(sK7(X0,X1,X6),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X6,X2,X0,X1] : (r2_hidden(sK7(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    spl8_6 | ~spl8_1 | ~spl8_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f93,f74,f70,f96])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_1 | ~spl8_2)),
% 0.21/0.46    inference(superposition,[],[f71,f91])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl8_2),
% 0.21/0.46    inference(resolution,[],[f58,f75])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    spl8_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f38,f86])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    spl8_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f82])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    v1_funct_1(sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    spl8_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f34,f78])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl8_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f35,f74])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    spl8_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f36,f70])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (10870)------------------------------
% 0.21/0.46  % (10870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (10870)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (10870)Memory used [KB]: 11001
% 0.21/0.46  % (10870)Time elapsed: 0.047 s
% 0.21/0.46  % (10870)------------------------------
% 0.21/0.46  % (10870)------------------------------
% 0.21/0.46  % (10863)Success in time 0.103 s
%------------------------------------------------------------------------------
