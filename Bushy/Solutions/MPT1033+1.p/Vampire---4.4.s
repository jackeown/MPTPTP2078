%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t142_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:31 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 374 expanded)
%              Number of leaves         :   48 ( 152 expanded)
%              Depth                    :   13
%              Number of atoms          :  579 (1438 expanded)
%              Number of equality atoms :   62 ( 179 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f406,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f79,f86,f93,f100,f107,f114,f121,f135,f145,f146,f162,f169,f179,f186,f210,f219,f227,f246,f259,f275,f312,f332,f340,f344,f348,f367,f386,f405])).

fof(f405,plain,
    ( spl6_66
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f388,f167,f403])).

fof(f403,plain,
    ( spl6_66
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f167,plain,
    ( spl6_26
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f388,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_26 ),
    inference(resolution,[],[f168,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t142_funct_2.p',t6_boole)).

fof(f168,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f167])).

fof(f386,plain,
    ( spl6_64
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f369,f157,f384])).

fof(f384,plain,
    ( spl6_64
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f157,plain,
    ( spl6_24
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f369,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_24 ),
    inference(resolution,[],[f158,f57])).

fof(f158,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f157])).

fof(f367,plain,
    ( spl6_62
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f350,f154,f365])).

fof(f365,plain,
    ( spl6_62
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f154,plain,
    ( spl6_22
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f350,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_22 ),
    inference(resolution,[],[f155,f57])).

fof(f155,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f154])).

fof(f348,plain,
    ( ~ spl6_37
    | spl6_60
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f298,f119,f105,f346,f214])).

fof(f214,plain,
    ( spl6_37
  <=> ~ v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f346,plain,
    ( spl6_60
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK3 = X1
        | ~ r1_partfun1(X1,sK3)
        | ~ v1_partfun1(X1,sK0)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f105,plain,
    ( spl6_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f119,plain,
    ( spl6_14
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f298,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ v1_partfun1(X1,sK0)
        | ~ v1_partfun1(sK3,sK0)
        | ~ r1_partfun1(X1,sK3)
        | sK3 = X1 )
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f294,f120])).

fof(f120,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f294,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X1)
        | ~ v1_partfun1(X1,sK0)
        | ~ v1_partfun1(sK3,sK0)
        | ~ r1_partfun1(X1,sK3)
        | sK3 = X1 )
    | ~ spl6_10 ),
    inference(resolution,[],[f61,f106])).

fof(f106,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_partfun1(X3,X0)
      | ~ r1_partfun1(X2,X3)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t142_funct_2.p',t148_partfun1)).

fof(f344,plain,
    ( ~ spl6_33
    | spl6_58
    | ~ spl6_0
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f296,f84,f70,f342,f199])).

fof(f199,plain,
    ( spl6_33
  <=> ~ v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f342,plain,
    ( spl6_58
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK2 = X0
        | ~ r1_partfun1(X0,sK2)
        | ~ v1_partfun1(X0,sK0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f70,plain,
    ( spl6_0
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f84,plain,
    ( spl6_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0)
        | ~ v1_partfun1(X0,sK0)
        | ~ v1_partfun1(sK2,sK0)
        | ~ r1_partfun1(X0,sK2)
        | sK2 = X0 )
    | ~ spl6_0
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f293,f85])).

fof(f85,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_partfun1(X0,sK0)
        | ~ v1_partfun1(sK2,sK0)
        | ~ r1_partfun1(X0,sK2)
        | sK2 = X0 )
    | ~ spl6_0 ),
    inference(resolution,[],[f61,f71])).

fof(f71,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f70])).

fof(f340,plain,
    ( ~ spl6_0
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_36
    | spl6_41 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_36
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f338,f242])).

fof(f242,plain,
    ( sK2 != sK3
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl6_41
  <=> sK2 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f338,plain,
    ( sK2 = sK3
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f337,f99])).

fof(f99,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_8
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f337,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | sK2 = sK3
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f336,f203])).

fof(f203,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl6_32
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f336,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ r1_partfun1(sK2,sK3)
    | sK2 = sK3
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f333,f85])).

fof(f333,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_partfun1(sK2,sK0)
    | ~ r1_partfun1(sK2,sK3)
    | sK2 = sK3
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_36 ),
    inference(resolution,[],[f299,f71])).

fof(f299,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ v1_partfun1(X1,sK0)
        | ~ r1_partfun1(X1,sK3)
        | sK3 = X1 )
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f298,f218])).

fof(f218,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl6_36
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f332,plain,
    ( ~ spl6_53
    | ~ spl6_55
    | ~ spl6_57
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_32
    | spl6_45 ),
    inference(avatar_split_clause,[],[f313,f254,f202,f84,f70,f330,f324,f318])).

fof(f318,plain,
    ( spl6_53
  <=> ~ r1_partfun1(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f324,plain,
    ( spl6_55
  <=> ~ v1_partfun1(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f330,plain,
    ( spl6_57
  <=> ~ v1_funct_1(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f254,plain,
    ( spl6_45
  <=> sK2 != sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f313,plain,
    ( ~ v1_funct_1(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ v1_partfun1(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK0)
    | ~ r1_partfun1(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK2)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_32
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f302,f255])).

fof(f255,plain,
    ( sK2 != sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f254])).

fof(f302,plain,
    ( ~ v1_funct_1(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ v1_partfun1(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK0)
    | ~ r1_partfun1(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK2)
    | sK2 = sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_32 ),
    inference(resolution,[],[f297,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t142_funct_2.p',existence_m1_subset_1)).

fof(f297,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0)
        | ~ v1_partfun1(X0,sK0)
        | ~ r1_partfun1(X0,sK2)
        | sK2 = X0 )
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f296,f203])).

fof(f312,plain,
    ( ~ spl6_51
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_36
    | spl6_41 ),
    inference(avatar_split_clause,[],[f305,f241,f217,f202,f119,f105,f84,f70,f310])).

fof(f310,plain,
    ( spl6_51
  <=> ~ r1_partfun1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f305,plain,
    ( ~ r1_partfun1(sK3,sK2)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_36
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f304,f242])).

fof(f304,plain,
    ( ~ r1_partfun1(sK3,sK2)
    | sK2 = sK3
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f303,f218])).

fof(f303,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ r1_partfun1(sK3,sK2)
    | sK2 = sK3
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f301,f120])).

fof(f301,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_partfun1(sK3,sK0)
    | ~ r1_partfun1(sK3,sK2)
    | sK2 = sK3
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(resolution,[],[f297,f106])).

fof(f275,plain,
    ( ~ spl6_47
    | spl6_48
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f262,f105,f273,f267])).

fof(f267,plain,
    ( spl6_47
  <=> ~ r2_relset_1(sK0,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f273,plain,
    ( spl6_48
  <=> sK3 = sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f262,plain,
    ( sK3 = sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f229,f58])).

fof(f229,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK3 = X1
        | ~ r2_relset_1(sK0,sK1,X1,sK3) )
    | ~ spl6_10 ),
    inference(resolution,[],[f53,f106])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t142_funct_2.p',redefinition_r2_relset_1)).

fof(f259,plain,
    ( ~ spl6_43
    | spl6_44
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f233,f70,f257,f251])).

fof(f251,plain,
    ( spl6_43
  <=> ~ r2_relset_1(sK0,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f257,plain,
    ( spl6_44
  <=> sK2 = sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f233,plain,
    ( sK2 = sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK2)
    | ~ spl6_0 ),
    inference(resolution,[],[f228,f58])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK2 = X0
        | ~ r2_relset_1(sK0,sK1,X0,sK2) )
    | ~ spl6_0 ),
    inference(resolution,[],[f53,f71])).

fof(f246,plain,
    ( ~ spl6_39
    | spl6_40
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f232,f105,f70,f244,f238])).

fof(f238,plain,
    ( spl6_39
  <=> ~ r2_relset_1(sK0,sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f244,plain,
    ( spl6_40
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f232,plain,
    ( sK2 = sK3
    | ~ r2_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(resolution,[],[f228,f106])).

fof(f227,plain,
    ( spl6_19
    | ~ spl6_34 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl6_19
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f225,f134])).

fof(f134,plain,
    ( k1_xboole_0 != sK1
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_19
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f225,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_34 ),
    inference(resolution,[],[f209,f57])).

fof(f209,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl6_34
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f219,plain,
    ( spl6_36
    | spl6_34
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f212,f119,f112,f105,f208,f217])).

fof(f112,plain,
    ( spl6_12
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f212,plain,
    ( v1_xboole_0(sK1)
    | v1_partfun1(sK3,sK0)
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f211,f113])).

fof(f113,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f211,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | v1_partfun1(sK3,sK0)
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f194,f120])).

fof(f194,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | v1_partfun1(sK3,sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f60,f106])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t142_funct_2.p',cc5_funct_2)).

fof(f210,plain,
    ( spl6_32
    | spl6_34
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f197,f84,f77,f70,f208,f202])).

fof(f77,plain,
    ( spl6_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f197,plain,
    ( v1_xboole_0(sK1)
    | v1_partfun1(sK2,sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f196,f78])).

fof(f78,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f196,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_partfun1(sK2,sK0)
    | ~ spl6_0
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f193,f85])).

fof(f193,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_partfun1(sK2,sK0)
    | ~ spl6_0 ),
    inference(resolution,[],[f60,f71])).

fof(f186,plain,
    ( spl6_30
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f171,f105,f184])).

fof(f184,plain,
    ( spl6_30
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f171,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f65,f106])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f179,plain,
    ( spl6_28
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f170,f70,f177])).

fof(f177,plain,
    ( spl6_28
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f170,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl6_0 ),
    inference(resolution,[],[f65,f71])).

fof(f169,plain,
    ( spl6_26
    | ~ spl6_25
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f148,f105,f160,f167])).

fof(f160,plain,
    ( spl6_25
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f148,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f59,f106])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t142_funct_2.p',cc3_relset_1)).

fof(f162,plain,
    ( spl6_22
    | ~ spl6_25
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f147,f70,f160,f154])).

fof(f147,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK2)
    | ~ spl6_0 ),
    inference(resolution,[],[f59,f71])).

fof(f146,plain,
    ( ~ spl6_21
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f137,f105,f143])).

fof(f143,plain,
    ( spl6_21
  <=> ~ sP5(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f137,plain,
    ( ~ sP5(sK1,sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f64,f106])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP5(X1,X0) ) ),
    inference(general_splitting,[],[f55,f63_D])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP5(X1,X0) ) ),
    inference(cnf_transformation,[],[f63_D])).

fof(f63_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP5(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t142_funct_2.p',reflexivity_r2_relset_1)).

fof(f145,plain,
    ( ~ spl6_21
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f136,f70,f143])).

fof(f136,plain,
    ( ~ sP5(sK1,sK0)
    | ~ spl6_0 ),
    inference(resolution,[],[f64,f71])).

fof(f135,plain,
    ( spl6_16
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f122,f133,f127])).

fof(f127,plain,
    ( spl6_16
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f122,plain,
    ( k1_xboole_0 != sK1
    | sK0 = sK1 ),
    inference(inner_rewriting,[],[f43])).

fof(f43,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t142_funct_2.p',t142_funct_2)).

fof(f121,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f44,f119])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f114,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f45,f112])).

fof(f45,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f107,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f46,f105])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f47,f98])).

fof(f47,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f91,plain,
    ( spl6_7
  <=> ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f48,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f49,f84])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f50,f77])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f51,f70])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
