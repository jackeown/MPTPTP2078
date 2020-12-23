%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 223 expanded)
%              Number of leaves         :   31 ( 104 expanded)
%              Depth                    :    7
%              Number of atoms          :  395 ( 873 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f321,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f64,f68,f72,f76,f84,f88,f92,f106,f161,f193,f204,f216,f251,f289,f299,f305,f311,f320])).

fof(f320,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_48 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_48 ),
    inference(subsumption_resolution,[],[f318,f63])).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f318,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(subsumption_resolution,[],[f317,f38])).

fof(f38,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_1
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f317,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK3))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(resolution,[],[f310,f53])).

fof(f53,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f310,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | r1_tarski(sK1,k3_subset_1(X0,sK3))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl4_48
  <=> ! [X0] :
        ( r1_tarski(sK1,k3_subset_1(X0,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f311,plain,
    ( spl4_48
    | ~ spl4_12
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f306,f302,f86,f309])).

fof(f86,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,k3_subset_1(X0,X2))
        | ~ r1_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f302,plain,
    ( spl4_47
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f306,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,k3_subset_1(X0,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl4_12
    | ~ spl4_47 ),
    inference(resolution,[],[f304,f87])).

fof(f87,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_tarski(X1,k3_subset_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f86])).

fof(f304,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f302])).

fof(f305,plain,
    ( spl4_47
    | ~ spl4_3
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f300,f297,f46,f302])).

fof(f46,plain,
    ( spl4_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f297,plain,
    ( spl4_46
  <=> ! [X1] :
        ( r1_xboole_0(X1,sK3)
        | ~ r1_tarski(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f300,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_3
    | ~ spl4_46 ),
    inference(resolution,[],[f298,f48])).

fof(f48,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f298,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK2)
        | r1_xboole_0(X1,sK3) )
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f297])).

fof(f299,plain,
    ( spl4_46
    | ~ spl4_13
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f291,f286,f90,f297])).

fof(f90,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f286,plain,
    ( spl4_44
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f291,plain,
    ( ! [X1] :
        ( r1_xboole_0(X1,sK3)
        | ~ r1_tarski(X1,sK2) )
    | ~ spl4_13
    | ~ spl4_44 ),
    inference(resolution,[],[f288,f91])).

fof(f91,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f288,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f286])).

fof(f289,plain,
    ( spl4_44
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f284,f248,f82,f56,f51,f286])).

fof(f56,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f82,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,X2)
        | ~ r1_tarski(X1,k3_subset_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f248,plain,
    ( spl4_37
  <=> r1_tarski(sK2,k3_subset_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f284,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f283,f58])).

fof(f58,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f283,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f282,f53])).

fof(f282,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(resolution,[],[f250,f83])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
        | r1_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f82])).

fof(f250,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK3))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f248])).

fof(f251,plain,
    ( spl4_37
    | ~ spl4_5
    | ~ spl4_30
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f246,f214,f201,f56,f248])).

fof(f201,plain,
    ( spl4_30
  <=> r1_tarski(sK3,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f214,plain,
    ( spl4_31
  <=> ! [X0] :
        ( ~ r1_tarski(sK3,k3_subset_1(sK0,X0))
        | r1_tarski(X0,k3_subset_1(sK0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f246,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK3))
    | ~ spl4_5
    | ~ spl4_30
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f242,f58])).

fof(f242,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_30
    | ~ spl4_31 ),
    inference(resolution,[],[f215,f203])).

fof(f203,plain,
    ( r1_tarski(sK3,k3_subset_1(sK0,sK2))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f201])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,k3_subset_1(sK0,X0))
        | r1_tarski(X0,k3_subset_1(sK0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( spl4_31
    | ~ spl4_9
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f212,f136,f103,f74,f214])).

fof(f74,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,X2)
        | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f103,plain,
    ( spl4_15
  <=> sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f136,plain,
    ( spl4_20
  <=> m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,k3_subset_1(sK0,X0))
        | r1_tarski(X0,k3_subset_1(sK0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_9
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f206,f137])).

fof(f137,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,k3_subset_1(sK0,X0))
        | r1_tarski(X0,k3_subset_1(sK0,sK3))
        | ~ m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(superposition,[],[f75,f105])).

fof(f105,plain,
    ( sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f103])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
        | r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f204,plain,
    ( spl4_30
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f199,f191,f56,f51,f201])).

fof(f191,plain,
    ( spl4_28
  <=> ! [X0] :
        ( r1_tarski(sK3,k3_subset_1(X0,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f199,plain,
    ( r1_tarski(sK3,k3_subset_1(sK0,sK2))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f198,f58])).

fof(f198,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK3,k3_subset_1(sK0,sK2))
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(resolution,[],[f192,f53])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | r1_tarski(sK3,k3_subset_1(X0,sK2)) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( spl4_28
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f188,f86,f41,f191])).

fof(f41,plain,
    ( spl4_2
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f188,plain,
    ( ! [X0] :
        ( r1_tarski(sK3,k3_subset_1(X0,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) )
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(resolution,[],[f87,f43])).

fof(f43,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f161,plain,
    ( ~ spl4_4
    | ~ spl4_7
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_7
    | spl4_20 ),
    inference(subsumption_resolution,[],[f159,f53])).

fof(f159,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl4_7
    | spl4_20 ),
    inference(resolution,[],[f138,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f138,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f106,plain,
    ( spl4_15
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f98,f70,f51,f103])).

fof(f70,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f98,plain,
    ( sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3))
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f71,f53])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f92,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f34,f90])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f88,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f32,f86])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f84,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f33,f82])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f72,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f68,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f64,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f22,f61])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
    & r1_xboole_0(sK3,sK2)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
                & r1_xboole_0(X3,X2)
                & r1_tarski(X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(sK1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
            & r1_xboole_0(X3,X2)
            & r1_tarski(sK1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ? [X3] :
          ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
          & r1_xboole_0(X3,sK2)
          & r1_tarski(sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
        & r1_xboole_0(X3,sK2)
        & r1_tarski(sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
      & r1_xboole_0(sK3,sK2)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ( r1_xboole_0(X3,X2)
                    & r1_tarski(X1,X2) )
                 => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ( r1_xboole_0(X3,X2)
                  & r1_tarski(X1,X2) )
               => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).

fof(f59,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f56])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f26,f41])).

fof(f26,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f27,f36])).

fof(f27,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:11:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.45  % (23700)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.45  % (23701)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.45  % (23699)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.45  % (23698)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.45  % (23699)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f321,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f64,f68,f72,f76,f84,f88,f92,f106,f161,f193,f204,f216,f251,f289,f299,f305,f311,f320])).
% 0.22/0.45  fof(f320,plain,(
% 0.22/0.45    spl4_1 | ~spl4_4 | ~spl4_6 | ~spl4_48),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f319])).
% 0.22/0.45  fof(f319,plain,(
% 0.22/0.45    $false | (spl4_1 | ~spl4_4 | ~spl4_6 | ~spl4_48)),
% 0.22/0.45    inference(subsumption_resolution,[],[f318,f63])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f61])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.45  fof(f318,plain,(
% 0.22/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl4_1 | ~spl4_4 | ~spl4_48)),
% 0.22/0.45    inference(subsumption_resolution,[],[f317,f38])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ~r1_tarski(sK1,k3_subset_1(sK0,sK3)) | spl4_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f36])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    spl4_1 <=> r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.45  fof(f317,plain,(
% 0.22/0.45    r1_tarski(sK1,k3_subset_1(sK0,sK3)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl4_4 | ~spl4_48)),
% 0.22/0.45    inference(resolution,[],[f310,f53])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f51])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.45  fof(f310,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK1,k3_subset_1(X0,sK3)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | ~spl4_48),
% 0.22/0.45    inference(avatar_component_clause,[],[f309])).
% 0.22/0.45  fof(f309,plain,(
% 0.22/0.45    spl4_48 <=> ! [X0] : (r1_tarski(sK1,k3_subset_1(X0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.22/0.45  fof(f311,plain,(
% 0.22/0.45    spl4_48 | ~spl4_12 | ~spl4_47),
% 0.22/0.45    inference(avatar_split_clause,[],[f306,f302,f86,f309])).
% 0.22/0.45  fof(f86,plain,(
% 0.22/0.45    spl4_12 <=> ! [X1,X0,X2] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.45  fof(f302,plain,(
% 0.22/0.45    spl4_47 <=> r1_xboole_0(sK1,sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.22/0.45  fof(f306,plain,(
% 0.22/0.45    ( ! [X0] : (r1_tarski(sK1,k3_subset_1(X0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | (~spl4_12 | ~spl4_47)),
% 0.22/0.45    inference(resolution,[],[f304,f87])).
% 0.22/0.45  fof(f87,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_12),
% 0.22/0.45    inference(avatar_component_clause,[],[f86])).
% 0.22/0.45  fof(f304,plain,(
% 0.22/0.45    r1_xboole_0(sK1,sK3) | ~spl4_47),
% 0.22/0.45    inference(avatar_component_clause,[],[f302])).
% 0.22/0.45  fof(f305,plain,(
% 0.22/0.45    spl4_47 | ~spl4_3 | ~spl4_46),
% 0.22/0.45    inference(avatar_split_clause,[],[f300,f297,f46,f302])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    spl4_3 <=> r1_tarski(sK1,sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.45  fof(f297,plain,(
% 0.22/0.45    spl4_46 <=> ! [X1] : (r1_xboole_0(X1,sK3) | ~r1_tarski(X1,sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.22/0.45  fof(f300,plain,(
% 0.22/0.45    r1_xboole_0(sK1,sK3) | (~spl4_3 | ~spl4_46)),
% 0.22/0.45    inference(resolution,[],[f298,f48])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    r1_tarski(sK1,sK2) | ~spl4_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f46])).
% 0.22/0.45  fof(f298,plain,(
% 0.22/0.45    ( ! [X1] : (~r1_tarski(X1,sK2) | r1_xboole_0(X1,sK3)) ) | ~spl4_46),
% 0.22/0.45    inference(avatar_component_clause,[],[f297])).
% 0.22/0.45  fof(f299,plain,(
% 0.22/0.45    spl4_46 | ~spl4_13 | ~spl4_44),
% 0.22/0.45    inference(avatar_split_clause,[],[f291,f286,f90,f297])).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    spl4_13 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.45  fof(f286,plain,(
% 0.22/0.45    spl4_44 <=> r1_xboole_0(sK2,sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.22/0.45  fof(f291,plain,(
% 0.22/0.45    ( ! [X1] : (r1_xboole_0(X1,sK3) | ~r1_tarski(X1,sK2)) ) | (~spl4_13 | ~spl4_44)),
% 0.22/0.45    inference(resolution,[],[f288,f91])).
% 0.22/0.45  fof(f91,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl4_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f90])).
% 0.22/0.45  fof(f288,plain,(
% 0.22/0.45    r1_xboole_0(sK2,sK3) | ~spl4_44),
% 0.22/0.45    inference(avatar_component_clause,[],[f286])).
% 0.22/0.45  fof(f289,plain,(
% 0.22/0.45    spl4_44 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_37),
% 0.22/0.45    inference(avatar_split_clause,[],[f284,f248,f82,f56,f51,f286])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    spl4_11 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.45  fof(f248,plain,(
% 0.22/0.45    spl4_37 <=> r1_tarski(sK2,k3_subset_1(sK0,sK3))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.22/0.45  fof(f284,plain,(
% 0.22/0.45    r1_xboole_0(sK2,sK3) | (~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_37)),
% 0.22/0.45    inference(subsumption_resolution,[],[f283,f58])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f56])).
% 0.22/0.45  fof(f283,plain,(
% 0.22/0.45    r1_xboole_0(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl4_4 | ~spl4_11 | ~spl4_37)),
% 0.22/0.45    inference(subsumption_resolution,[],[f282,f53])).
% 0.22/0.45  fof(f282,plain,(
% 0.22/0.45    r1_xboole_0(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl4_11 | ~spl4_37)),
% 0.22/0.45    inference(resolution,[],[f250,f83])).
% 0.22/0.45  fof(f83,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_11),
% 0.22/0.45    inference(avatar_component_clause,[],[f82])).
% 0.22/0.45  fof(f250,plain,(
% 0.22/0.45    r1_tarski(sK2,k3_subset_1(sK0,sK3)) | ~spl4_37),
% 0.22/0.45    inference(avatar_component_clause,[],[f248])).
% 0.22/0.45  fof(f251,plain,(
% 0.22/0.45    spl4_37 | ~spl4_5 | ~spl4_30 | ~spl4_31),
% 0.22/0.45    inference(avatar_split_clause,[],[f246,f214,f201,f56,f248])).
% 0.22/0.45  fof(f201,plain,(
% 0.22/0.45    spl4_30 <=> r1_tarski(sK3,k3_subset_1(sK0,sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.45  fof(f214,plain,(
% 0.22/0.45    spl4_31 <=> ! [X0] : (~r1_tarski(sK3,k3_subset_1(sK0,X0)) | r1_tarski(X0,k3_subset_1(sK0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.45  fof(f246,plain,(
% 0.22/0.45    r1_tarski(sK2,k3_subset_1(sK0,sK3)) | (~spl4_5 | ~spl4_30 | ~spl4_31)),
% 0.22/0.45    inference(subsumption_resolution,[],[f242,f58])).
% 0.22/0.45  fof(f242,plain,(
% 0.22/0.45    r1_tarski(sK2,k3_subset_1(sK0,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl4_30 | ~spl4_31)),
% 0.22/0.45    inference(resolution,[],[f215,f203])).
% 0.22/0.45  fof(f203,plain,(
% 0.22/0.45    r1_tarski(sK3,k3_subset_1(sK0,sK2)) | ~spl4_30),
% 0.22/0.45    inference(avatar_component_clause,[],[f201])).
% 0.22/0.45  fof(f215,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(sK3,k3_subset_1(sK0,X0)) | r1_tarski(X0,k3_subset_1(sK0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl4_31),
% 0.22/0.45    inference(avatar_component_clause,[],[f214])).
% 0.22/0.45  fof(f216,plain,(
% 0.22/0.45    spl4_31 | ~spl4_9 | ~spl4_15 | ~spl4_20),
% 0.22/0.45    inference(avatar_split_clause,[],[f212,f136,f103,f74,f214])).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    spl4_9 <=> ! [X1,X0,X2] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.45  fof(f103,plain,(
% 0.22/0.45    spl4_15 <=> sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.45  fof(f136,plain,(
% 0.22/0.45    spl4_20 <=> m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.45  fof(f212,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(sK3,k3_subset_1(sK0,X0)) | r1_tarski(X0,k3_subset_1(sK0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | (~spl4_9 | ~spl4_15 | ~spl4_20)),
% 0.22/0.45    inference(subsumption_resolution,[],[f206,f137])).
% 0.22/0.45  fof(f137,plain,(
% 0.22/0.45    m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0)) | ~spl4_20),
% 0.22/0.45    inference(avatar_component_clause,[],[f136])).
% 0.22/0.45  fof(f206,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(sK3,k3_subset_1(sK0,X0)) | r1_tarski(X0,k3_subset_1(sK0,sK3)) | ~m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | (~spl4_9 | ~spl4_15)),
% 0.22/0.45    inference(superposition,[],[f75,f105])).
% 0.22/0.45  fof(f105,plain,(
% 0.22/0.45    sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3)) | ~spl4_15),
% 0.22/0.45    inference(avatar_component_clause,[],[f103])).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f74])).
% 0.22/0.45  fof(f204,plain,(
% 0.22/0.45    spl4_30 | ~spl4_4 | ~spl4_5 | ~spl4_28),
% 0.22/0.45    inference(avatar_split_clause,[],[f199,f191,f56,f51,f201])).
% 0.22/0.45  fof(f191,plain,(
% 0.22/0.45    spl4_28 <=> ! [X0] : (r1_tarski(sK3,k3_subset_1(X0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.45  fof(f199,plain,(
% 0.22/0.45    r1_tarski(sK3,k3_subset_1(sK0,sK2)) | (~spl4_4 | ~spl4_5 | ~spl4_28)),
% 0.22/0.45    inference(subsumption_resolution,[],[f198,f58])).
% 0.22/0.45  fof(f198,plain,(
% 0.22/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK3,k3_subset_1(sK0,sK2)) | (~spl4_4 | ~spl4_28)),
% 0.22/0.45    inference(resolution,[],[f192,f53])).
% 0.22/0.45  fof(f192,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(sK3,k3_subset_1(X0,sK2))) ) | ~spl4_28),
% 0.22/0.45    inference(avatar_component_clause,[],[f191])).
% 0.22/0.45  fof(f193,plain,(
% 0.22/0.45    spl4_28 | ~spl4_2 | ~spl4_12),
% 0.22/0.45    inference(avatar_split_clause,[],[f188,f86,f41,f191])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    spl4_2 <=> r1_xboole_0(sK3,sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.45  fof(f188,plain,(
% 0.22/0.45    ( ! [X0] : (r1_tarski(sK3,k3_subset_1(X0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0))) ) | (~spl4_2 | ~spl4_12)),
% 0.22/0.45    inference(resolution,[],[f87,f43])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    r1_xboole_0(sK3,sK2) | ~spl4_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f41])).
% 0.22/0.45  fof(f161,plain,(
% 0.22/0.45    ~spl4_4 | ~spl4_7 | spl4_20),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f160])).
% 0.22/0.45  fof(f160,plain,(
% 0.22/0.45    $false | (~spl4_4 | ~spl4_7 | spl4_20)),
% 0.22/0.45    inference(subsumption_resolution,[],[f159,f53])).
% 0.22/0.45  fof(f159,plain,(
% 0.22/0.45    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl4_7 | spl4_20)),
% 0.22/0.45    inference(resolution,[],[f138,f67])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f66])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    spl4_7 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.45  fof(f138,plain,(
% 0.22/0.45    ~m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0)) | spl4_20),
% 0.22/0.45    inference(avatar_component_clause,[],[f136])).
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    spl4_15 | ~spl4_4 | ~spl4_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f98,f70,f51,f103])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    spl4_8 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3)) | (~spl4_4 | ~spl4_8)),
% 0.22/0.45    inference(resolution,[],[f71,f53])).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) ) | ~spl4_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f70])).
% 0.22/0.45  fof(f92,plain,(
% 0.22/0.45    spl4_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f34,f90])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(flattening,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.46  fof(f88,plain,(
% 0.22/0.46    spl4_12),
% 0.22/0.46    inference(avatar_split_clause,[],[f32,f86])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(nnf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.22/0.46  fof(f84,plain,(
% 0.22/0.46    spl4_11),
% 0.22/0.46    inference(avatar_split_clause,[],[f33,f82])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f76,plain,(
% 0.22/0.46    spl4_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f31,f74])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(nnf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    spl4_8),
% 0.22/0.46    inference(avatar_split_clause,[],[f29,f70])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    spl4_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f28,f66])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.46  fof(f64,plain,(
% 0.22/0.46    spl4_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f22,f61])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ((~r1_tarski(sK1,k3_subset_1(sK0,sK3)) & r1_xboole_0(sK3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f18,f17,f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ? [X2] : (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (~r1_tarski(sK1,k3_subset_1(sK0,sK3)) & r1_xboole_0(sK3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(flattening,[],[f8])).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(X1,k3_subset_1(X0,X3)) & (r1_xboole_0(X3,X2) & r1_tarski(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.22/0.46    inference(negated_conjecture,[],[f6])).
% 0.22/0.46  fof(f6,conjecture,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    spl4_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f23,f56])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    spl4_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f24,f51])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    spl4_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f25,f46])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    r1_tarski(sK1,sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    spl4_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f26,f41])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    r1_xboole_0(sK3,sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ~spl4_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f27,f36])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ~r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (23699)------------------------------
% 0.22/0.46  % (23699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (23699)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (23699)Memory used [KB]: 10746
% 0.22/0.46  % (23699)Time elapsed: 0.009 s
% 0.22/0.46  % (23699)------------------------------
% 0.22/0.46  % (23699)------------------------------
% 0.22/0.46  % (23693)Success in time 0.087 s
%------------------------------------------------------------------------------
