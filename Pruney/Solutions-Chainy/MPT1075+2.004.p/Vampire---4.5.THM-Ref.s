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
% DateTime   : Thu Dec  3 13:08:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 359 expanded)
%              Number of leaves         :   37 ( 144 expanded)
%              Depth                    :   15
%              Number of atoms          :  747 (1435 expanded)
%              Number of equality atoms :   80 ( 137 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (16410)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (16413)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f399,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f83,f96,f101,f106,f121,f126,f131,f142,f157,f167,f172,f204,f220,f247,f286,f289,f309,f335,f376,f384,f391,f398])).

fof(f398,plain,
    ( ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | spl6_44 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | spl6_44 ),
    inference(subsumption_resolution,[],[f396,f67])).

fof(f67,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl6_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f396,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | spl6_44 ),
    inference(subsumption_resolution,[],[f395,f77])).

fof(f77,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_5
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f395,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9
    | spl6_44 ),
    inference(subsumption_resolution,[],[f394,f105])).

fof(f105,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f394,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_2
    | ~ spl6_7
    | spl6_44 ),
    inference(subsumption_resolution,[],[f393,f95])).

fof(f95,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f393,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_2
    | spl6_44 ),
    inference(trivial_inequality_removal,[],[f392])).

fof(f392,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_2
    | spl6_44 ),
    inference(superposition,[],[f390,f91])).

fof(f91,plain,
    ( ! [X14,X12,X13] :
        ( k3_funct_2(X12,X13,sK3,X14) = k1_funct_1(sK3,X14)
        | ~ v1_funct_2(sK3,X12,X13)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | ~ m1_subset_1(X14,X12)
        | v1_xboole_0(X12) )
    | ~ spl6_2 ),
    inference(resolution,[],[f62,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f62,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f390,plain,
    ( k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_44 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl6_44
  <=> k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f391,plain,
    ( ~ spl6_44
    | spl6_10
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f386,f381,f118,f388])).

fof(f118,plain,
    ( spl6_10
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f381,plain,
    ( spl6_43
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f386,plain,
    ( k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_10
    | ~ spl6_43 ),
    inference(superposition,[],[f120,f383])).

fof(f383,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f381])).

fof(f120,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f384,plain,
    ( spl6_43
    | spl6_3
    | ~ spl6_5
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_36
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f379,f365,f306,f244,f217,f75,f65,f381])).

fof(f217,plain,
    ( spl6_23
  <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f244,plain,
    ( spl6_26
  <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f306,plain,
    ( spl6_36
  <=> k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f365,plain,
    ( spl6_42
  <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f379,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_3
    | ~ spl6_5
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_36
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f378,f308])).

fof(f308,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f306])).

fof(f378,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_3
    | ~ spl6_5
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(resolution,[],[f377,f77])).

fof(f377,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | spl6_3
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f370,f366])).

fof(f366,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f365])).

fof(f370,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | spl6_3
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f369,f67])).

fof(f369,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(resolution,[],[f242,f246])).

fof(f246,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f244])).

fof(f242,plain,
    ( ! [X14,X12,X13] :
        ( ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X12,X13)
        | v1_xboole_0(X12)
        | ~ m1_subset_1(X14,X12)
        | k3_funct_2(X12,X13,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X14) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X14) )
    | ~ spl6_23 ),
    inference(resolution,[],[f219,f49])).

fof(f219,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f217])).

fof(f376,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_42 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_42 ),
    inference(subsumption_resolution,[],[f374,f95])).

fof(f374,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | spl6_42 ),
    inference(subsumption_resolution,[],[f373,f100])).

fof(f100,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f373,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_9
    | spl6_42 ),
    inference(subsumption_resolution,[],[f372,f57])).

fof(f57,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f372,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_2
    | ~ spl6_9
    | spl6_42 ),
    inference(subsumption_resolution,[],[f371,f105])).

fof(f371,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_2
    | spl6_42 ),
    inference(resolution,[],[f367,f89])).

fof(f89,plain,
    ( ! [X6,X4,X7,X5] :
        ( v1_funct_2(k8_funct_2(X4,X5,X7,sK3,X6),X4,X7)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X7)))
        | ~ v1_funct_2(sK3,X4,X5) )
    | ~ spl6_2 ),
    inference(resolution,[],[f62,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f367,plain,
    ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | spl6_42 ),
    inference(avatar_component_clause,[],[f365])).

fof(f335,plain,
    ( spl6_3
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl6_3
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f319,f38])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f319,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_24 ),
    inference(superposition,[],[f67,f233])).

fof(f233,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl6_24
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f309,plain,
    ( spl6_36
    | ~ spl6_5
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f294,f280,f75,f306])).

fof(f280,plain,
    ( spl6_32
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f294,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_5
    | ~ spl6_32 ),
    inference(resolution,[],[f281,f77])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f280])).

fof(f289,plain,
    ( ~ spl6_12
    | ~ spl6_16
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl6_12
    | ~ spl6_16
    | spl6_33 ),
    inference(subsumption_resolution,[],[f287,f156])).

fof(f156,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_16
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f287,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ spl6_12
    | spl6_33 ),
    inference(resolution,[],[f285,f137])).

fof(f137,plain,
    ( ! [X2] :
        ( r1_tarski(k2_relat_1(sK3),X2)
        | ~ v5_relat_1(sK3,X2) )
    | ~ spl6_12 ),
    inference(resolution,[],[f130,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f130,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f285,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl6_33 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl6_33
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f286,plain,
    ( spl6_32
    | ~ spl6_33
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_21
    | spl6_24 ),
    inference(avatar_split_clause,[],[f252,f231,f201,f169,f164,f103,f98,f93,f70,f60,f55,f283,f280])).

fof(f70,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f164,plain,
    ( spl6_18
  <=> k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f169,plain,
    ( spl6_19
  <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f201,plain,
    ( spl6_21
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_21
    | spl6_24 ),
    inference(subsumption_resolution,[],[f251,f232])).

fof(f232,plain,
    ( k1_xboole_0 != sK1
    | spl6_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f250,f105])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f249,f95])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f248,f62])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(superposition,[],[f238,f171])).

fof(f171,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f169])).

fof(f238,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ m1_subset_1(X2,X0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f184,f203])).

fof(f203,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f201])).

fof(f184,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ m1_subset_1(X2,X0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f183,f72])).

fof(f72,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f183,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(sK0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f182,f100])).

fof(f182,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(sK0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_1
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f181,f57])).

fof(f181,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(sK0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_18 ),
    inference(superposition,[],[f43,f166])).

fof(f166,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | v1_xboole_0(X2)
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f247,plain,
    ( spl6_26
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f223,f103,f98,f93,f60,f55,f244])).

fof(f223,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f222,f57])).

fof(f222,plain,
    ( ~ v1_funct_1(sK4)
    | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f210,f100])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0)
        | m1_subset_1(k8_funct_2(sK1,sK0,X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f209,f95])).

% (16406)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | m1_subset_1(k8_funct_2(sK1,sK0,X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(resolution,[],[f90,f105])).

fof(f90,plain,
    ( ! [X10,X8,X11,X9] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_2(sK3,X8,X9)
        | ~ v1_funct_1(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X11)))
        | m1_subset_1(k8_funct_2(X8,X9,X11,sK3,X10),k1_zfmisc_1(k2_zfmisc_1(X8,X11))) )
    | ~ spl6_2 ),
    inference(resolution,[],[f62,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f220,plain,
    ( spl6_23
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f215,f103,f98,f93,f60,f55,f217])).

fof(f215,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f214,f57])).

fof(f214,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f196,f100])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0)
        | v1_funct_1(k8_funct_2(sK1,sK0,X1,sK3,X0)) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f195,f95])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | v1_funct_1(k8_funct_2(sK1,sK0,X1,sK3,X0)) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(resolution,[],[f88,f105])).

fof(f88,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | v1_funct_1(k8_funct_2(X0,X1,X3,sK3,X2)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f62,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f204,plain,
    ( spl6_21
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f199,f139,f123,f80,f201])).

fof(f80,plain,
    ( spl6_6
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f123,plain,
    ( spl6_11
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f139,plain,
    ( spl6_13
  <=> v4_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f199,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f198,f82])).

fof(f82,plain,
    ( v1_partfun1(sK4,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f198,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ v1_partfun1(sK4,sK0)
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(resolution,[],[f132,f141])).

fof(f141,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK4,X0)
        | k1_relat_1(sK4) = X0
        | ~ v1_partfun1(sK4,X0) )
    | ~ spl6_11 ),
    inference(resolution,[],[f125,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f125,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f172,plain,
    ( spl6_19
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f114,f103,f169])).

fof(f114,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl6_9 ),
    inference(resolution,[],[f105,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f167,plain,
    ( spl6_18
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f110,f98,f164])).

fof(f110,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f100,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f157,plain,
    ( spl6_16
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f113,f103,f154])).

fof(f113,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f105,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f142,plain,
    ( spl6_13
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f107,f98,f139])).

fof(f107,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f100,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f131,plain,
    ( spl6_12
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f116,f103,f128])).

fof(f116,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_9 ),
    inference(resolution,[],[f105,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f126,plain,
    ( spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f111,f98,f123])).

fof(f111,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f100,f44])).

fof(f121,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f30,f118])).

fof(f30,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

fof(f106,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f35,f103])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f101,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f32,f98])).

fof(f32,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f96,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f34,f93])).

fof(f34,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f29,f80])).

fof(f29,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f28,f75])).

fof(f28,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f37,f70])).

fof(f37,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f31,f55])).

fof(f31,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:12:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (16407)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (16412)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (16404)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (16409)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (16407)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (16418)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.53  % (16421)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  % (16411)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.53  % (16415)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (16419)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (16417)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.54  % (16417)Refutation not found, incomplete strategy% (16417)------------------------------
% 0.21/0.54  % (16417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16417)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16417)Memory used [KB]: 1663
% 0.21/0.54  % (16417)Time elapsed: 0.105 s
% 0.21/0.54  % (16417)------------------------------
% 0.21/0.54  % (16417)------------------------------
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  % (16410)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.54  % (16413)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.54  fof(f399,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f83,f96,f101,f106,f121,f126,f131,f142,f157,f167,f172,f204,f220,f247,f286,f289,f309,f335,f376,f384,f391,f398])).
% 0.21/0.54  fof(f398,plain,(
% 0.21/0.54    ~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9 | spl6_44),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f397])).
% 0.21/0.54  fof(f397,plain,(
% 0.21/0.54    $false | (~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9 | spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f396,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ~v1_xboole_0(sK1) | spl6_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    spl6_3 <=> v1_xboole_0(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.54  fof(f396,plain,(
% 0.21/0.54    v1_xboole_0(sK1) | (~spl6_2 | ~spl6_5 | ~spl6_7 | ~spl6_9 | spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f395,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    m1_subset_1(sK5,sK1) | ~spl6_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl6_5 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.54  fof(f395,plain,(
% 0.21/0.54    ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | (~spl6_2 | ~spl6_7 | ~spl6_9 | spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f394,f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    spl6_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.54  fof(f394,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | (~spl6_2 | ~spl6_7 | spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f393,f95])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    v1_funct_2(sK3,sK1,sK0) | ~spl6_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f93])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    spl6_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.54  fof(f393,plain,(
% 0.21/0.54    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | (~spl6_2 | spl6_44)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f392])).
% 0.21/0.54  fof(f392,plain,(
% 0.21/0.54    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | (~spl6_2 | spl6_44)),
% 0.21/0.54    inference(superposition,[],[f390,f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X14,X12,X13] : (k3_funct_2(X12,X13,sK3,X14) = k1_funct_1(sK3,X14) | ~v1_funct_2(sK3,X12,X13) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~m1_subset_1(X14,X12) | v1_xboole_0(X12)) ) | ~spl6_2),
% 0.21/0.54    inference(resolution,[],[f62,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    v1_funct_1(sK3) | ~spl6_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    spl6_2 <=> v1_funct_1(sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.54  fof(f390,plain,(
% 0.21/0.54    k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl6_44),
% 0.21/0.54    inference(avatar_component_clause,[],[f388])).
% 0.21/0.54  fof(f388,plain,(
% 0.21/0.54    spl6_44 <=> k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.54  fof(f391,plain,(
% 0.21/0.54    ~spl6_44 | spl6_10 | ~spl6_43),
% 0.21/0.54    inference(avatar_split_clause,[],[f386,f381,f118,f388])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    spl6_10 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    spl6_43 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.54  fof(f386,plain,(
% 0.21/0.54    k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_10 | ~spl6_43)),
% 0.21/0.54    inference(superposition,[],[f120,f383])).
% 0.21/0.54  fof(f383,plain,(
% 0.21/0.54    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl6_43),
% 0.21/0.54    inference(avatar_component_clause,[],[f381])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | spl6_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f118])).
% 0.21/0.54  fof(f384,plain,(
% 0.21/0.54    spl6_43 | spl6_3 | ~spl6_5 | ~spl6_23 | ~spl6_26 | ~spl6_36 | ~spl6_42),
% 0.21/0.54    inference(avatar_split_clause,[],[f379,f365,f306,f244,f217,f75,f65,f381])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    spl6_23 <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    spl6_26 <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    spl6_36 <=> k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.54  fof(f365,plain,(
% 0.21/0.54    spl6_42 <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.54  fof(f379,plain,(
% 0.21/0.54    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_3 | ~spl6_5 | ~spl6_23 | ~spl6_26 | ~spl6_36 | ~spl6_42)),
% 0.21/0.54    inference(forward_demodulation,[],[f378,f308])).
% 0.21/0.54  fof(f308,plain,(
% 0.21/0.54    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl6_36),
% 0.21/0.54    inference(avatar_component_clause,[],[f306])).
% 0.21/0.54  fof(f378,plain,(
% 0.21/0.54    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | (spl6_3 | ~spl6_5 | ~spl6_23 | ~spl6_26 | ~spl6_42)),
% 0.21/0.54    inference(resolution,[],[f377,f77])).
% 0.21/0.54  fof(f377,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (spl6_3 | ~spl6_23 | ~spl6_26 | ~spl6_42)),
% 0.21/0.54    inference(subsumption_resolution,[],[f370,f366])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~spl6_42),
% 0.21/0.54    inference(avatar_component_clause,[],[f365])).
% 0.21/0.54  fof(f370,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (spl6_3 | ~spl6_23 | ~spl6_26)),
% 0.21/0.54    inference(subsumption_resolution,[],[f369,f67])).
% 0.21/0.54  fof(f369,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (~spl6_23 | ~spl6_26)),
% 0.21/0.54    inference(resolution,[],[f242,f246])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_26),
% 0.21/0.54    inference(avatar_component_clause,[],[f244])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    ( ! [X14,X12,X13] : (~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X12,X13) | v1_xboole_0(X12) | ~m1_subset_1(X14,X12) | k3_funct_2(X12,X13,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X14) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X14)) ) | ~spl6_23),
% 0.21/0.54    inference(resolution,[],[f219,f49])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~spl6_23),
% 0.21/0.54    inference(avatar_component_clause,[],[f217])).
% 0.21/0.54  fof(f376,plain,(
% 0.21/0.54    ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_42),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f375])).
% 0.21/0.54  fof(f375,plain,(
% 0.21/0.54    $false | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_42)),
% 0.21/0.54    inference(subsumption_resolution,[],[f374,f95])).
% 0.21/0.54  fof(f374,plain,(
% 0.21/0.54    ~v1_funct_2(sK3,sK1,sK0) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | spl6_42)),
% 0.21/0.54    inference(subsumption_resolution,[],[f373,f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.54  fof(f373,plain,(
% 0.21/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl6_1 | ~spl6_2 | ~spl6_9 | spl6_42)),
% 0.21/0.54    inference(subsumption_resolution,[],[f372,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    v1_funct_1(sK4) | ~spl6_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    spl6_1 <=> v1_funct_1(sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.54  fof(f372,plain,(
% 0.21/0.54    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl6_2 | ~spl6_9 | spl6_42)),
% 0.21/0.54    inference(subsumption_resolution,[],[f371,f105])).
% 0.21/0.54  fof(f371,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl6_2 | spl6_42)),
% 0.21/0.54    inference(resolution,[],[f367,f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X6,X4,X7,X5] : (v1_funct_2(k8_funct_2(X4,X5,X7,sK3,X6),X4,X7) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X7))) | ~v1_funct_2(sK3,X4,X5)) ) | ~spl6_2),
% 0.21/0.54    inference(resolution,[],[f62,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).
% 0.21/0.54  fof(f367,plain,(
% 0.21/0.54    ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | spl6_42),
% 0.21/0.54    inference(avatar_component_clause,[],[f365])).
% 0.21/0.54  fof(f335,plain,(
% 0.21/0.54    spl6_3 | ~spl6_24),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f334])).
% 0.21/0.54  fof(f334,plain,(
% 0.21/0.54    $false | (spl6_3 | ~spl6_24)),
% 0.21/0.54    inference(subsumption_resolution,[],[f319,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f319,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_24)),
% 0.21/0.54    inference(superposition,[],[f67,f233])).
% 0.21/0.54  fof(f233,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl6_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f231])).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    spl6_24 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.54  fof(f309,plain,(
% 0.21/0.54    spl6_36 | ~spl6_5 | ~spl6_32),
% 0.21/0.54    inference(avatar_split_clause,[],[f294,f280,f75,f306])).
% 0.21/0.54  fof(f280,plain,(
% 0.21/0.54    spl6_32 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.54  fof(f294,plain,(
% 0.21/0.54    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_5 | ~spl6_32)),
% 0.21/0.54    inference(resolution,[],[f281,f77])).
% 0.21/0.54  fof(f281,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | ~spl6_32),
% 0.21/0.54    inference(avatar_component_clause,[],[f280])).
% 0.21/0.54  fof(f289,plain,(
% 0.21/0.54    ~spl6_12 | ~spl6_16 | spl6_33),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f288])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    $false | (~spl6_12 | ~spl6_16 | spl6_33)),
% 0.21/0.54    inference(subsumption_resolution,[],[f287,f156])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    v5_relat_1(sK3,sK0) | ~spl6_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f154])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    spl6_16 <=> v5_relat_1(sK3,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.54  fof(f287,plain,(
% 0.21/0.54    ~v5_relat_1(sK3,sK0) | (~spl6_12 | spl6_33)),
% 0.21/0.54    inference(resolution,[],[f285,f137])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X2] : (r1_tarski(k2_relat_1(sK3),X2) | ~v5_relat_1(sK3,X2)) ) | ~spl6_12),
% 0.21/0.54    inference(resolution,[],[f130,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    v1_relat_1(sK3) | ~spl6_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f128])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    spl6_12 <=> v1_relat_1(sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.54  fof(f285,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(sK3),sK0) | spl6_33),
% 0.21/0.54    inference(avatar_component_clause,[],[f283])).
% 0.21/0.54  fof(f283,plain,(
% 0.21/0.54    spl6_33 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.54  fof(f286,plain,(
% 0.21/0.54    spl6_32 | ~spl6_33 | ~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_18 | ~spl6_19 | ~spl6_21 | spl6_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f252,f231,f201,f169,f164,f103,f98,f93,f70,f60,f55,f283,f280])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    spl6_4 <=> v1_xboole_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    spl6_18 <=> k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    spl6_19 <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    spl6_21 <=> sK0 = k1_relat_1(sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_18 | ~spl6_19 | ~spl6_21 | spl6_24)),
% 0.21/0.54    inference(subsumption_resolution,[],[f251,f232])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | spl6_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f231])).
% 0.21/0.54  fof(f251,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_18 | ~spl6_19 | ~spl6_21)),
% 0.21/0.54    inference(subsumption_resolution,[],[f250,f105])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_18 | ~spl6_19 | ~spl6_21)),
% 0.21/0.54    inference(subsumption_resolution,[],[f249,f95])).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_18 | ~spl6_19 | ~spl6_21)),
% 0.21/0.54    inference(subsumption_resolution,[],[f248,f62])).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_18 | ~spl6_19 | ~spl6_21)),
% 0.21/0.54    inference(superposition,[],[f238,f171])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) | ~spl6_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f169])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(X2,X0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))) ) | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_18 | ~spl6_21)),
% 0.21/0.54    inference(forward_demodulation,[],[f184,f203])).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    sK0 = k1_relat_1(sK4) | ~spl6_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f201])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(X2,X0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))) ) | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f183,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ~v1_xboole_0(sK0) | spl6_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f70])).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(X2,X0) | v1_xboole_0(sK0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))) ) | (~spl6_1 | ~spl6_8 | ~spl6_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f182,f100])).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X2,X0) | v1_xboole_0(sK0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))) ) | (~spl6_1 | ~spl6_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f181,f57])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X2,X0) | v1_xboole_0(sK0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))) ) | ~spl6_18),
% 0.21/0.54    inference(superposition,[],[f43,f166])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) | ~spl6_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f164])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | v1_xboole_0(X2) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.54  fof(f247,plain,(
% 0.21/0.54    spl6_26 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f223,f103,f98,f93,f60,f55,f244])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.54    inference(subsumption_resolution,[],[f222,f57])).
% 0.21/0.54  fof(f222,plain,(
% 0.21/0.54    ~v1_funct_1(sK4) | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.54    inference(resolution,[],[f210,f100])).
% 0.21/0.54  fof(f210,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0) | m1_subset_1(k8_funct_2(sK1,sK0,X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.54    inference(subsumption_resolution,[],[f209,f95])).
% 0.21/0.54  % (16406)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | m1_subset_1(k8_funct_2(sK1,sK0,X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl6_2 | ~spl6_9)),
% 0.21/0.54    inference(resolution,[],[f90,f105])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(sK3,X8,X9) | ~v1_funct_1(X10) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X11))) | m1_subset_1(k8_funct_2(X8,X9,X11,sK3,X10),k1_zfmisc_1(k2_zfmisc_1(X8,X11)))) ) | ~spl6_2),
% 0.21/0.54    inference(resolution,[],[f62,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    spl6_23 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f215,f103,f98,f93,f60,f55,f217])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.54    inference(subsumption_resolution,[],[f214,f57])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    ~v1_funct_1(sK4) | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | (~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.54    inference(resolution,[],[f196,f100])).
% 0.21/0.54  fof(f196,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0) | v1_funct_1(k8_funct_2(sK1,sK0,X1,sK3,X0))) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.54    inference(subsumption_resolution,[],[f195,f95])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | v1_funct_1(k8_funct_2(sK1,sK0,X1,sK3,X0))) ) | (~spl6_2 | ~spl6_9)),
% 0.21/0.54    inference(resolution,[],[f88,f105])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_funct_1(k8_funct_2(X0,X1,X3,sK3,X2))) ) | ~spl6_2),
% 0.21/0.54    inference(resolution,[],[f62,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    spl6_21 | ~spl6_6 | ~spl6_11 | ~spl6_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f199,f139,f123,f80,f201])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl6_6 <=> v1_partfun1(sK4,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    spl6_11 <=> v1_relat_1(sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    spl6_13 <=> v4_relat_1(sK4,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.54  fof(f199,plain,(
% 0.21/0.54    sK0 = k1_relat_1(sK4) | (~spl6_6 | ~spl6_11 | ~spl6_13)),
% 0.21/0.54    inference(subsumption_resolution,[],[f198,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    v1_partfun1(sK4,sK0) | ~spl6_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f80])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    sK0 = k1_relat_1(sK4) | ~v1_partfun1(sK4,sK0) | (~spl6_11 | ~spl6_13)),
% 0.21/0.54    inference(resolution,[],[f132,f141])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    v4_relat_1(sK4,sK0) | ~spl6_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f139])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ( ! [X0] : (~v4_relat_1(sK4,X0) | k1_relat_1(sK4) = X0 | ~v1_partfun1(sK4,X0)) ) | ~spl6_11),
% 0.21/0.54    inference(resolution,[],[f125,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    v1_relat_1(sK4) | ~spl6_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f123])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    spl6_19 | ~spl6_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f114,f103,f169])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) | ~spl6_9),
% 0.21/0.54    inference(resolution,[],[f105,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    spl6_18 | ~spl6_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f110,f98,f164])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) | ~spl6_8),
% 0.21/0.54    inference(resolution,[],[f100,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    spl6_16 | ~spl6_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f113,f103,f154])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    v5_relat_1(sK3,sK0) | ~spl6_9),
% 0.21/0.54    inference(resolution,[],[f105,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    spl6_13 | ~spl6_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f107,f98,f139])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    v4_relat_1(sK4,sK0) | ~spl6_8),
% 0.21/0.54    inference(resolution,[],[f100,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    spl6_12 | ~spl6_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f116,f103,f128])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    v1_relat_1(sK3) | ~spl6_9),
% 0.21/0.54    inference(resolution,[],[f105,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    spl6_11 | ~spl6_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f111,f98,f123])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    v1_relat_1(sK4) | ~spl6_8),
% 0.21/0.54    inference(resolution,[],[f100,f44])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ~spl6_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f30,f118])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f11])).
% 0.21/0.54  fof(f11,conjecture,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    spl6_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f35,f103])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    spl6_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f32,f98])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    spl6_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f34,f93])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    spl6_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f29,f80])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    v1_partfun1(sK4,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    spl6_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f28,f75])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    m1_subset_1(sK5,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ~spl6_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f37,f70])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ~spl6_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f36,f65])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ~v1_xboole_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    spl6_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f33,f60])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    v1_funct_1(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    spl6_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f31,f55])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    v1_funct_1(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (16407)------------------------------
% 0.21/0.54  % (16407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16407)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (16407)Memory used [KB]: 10874
% 0.21/0.54  % (16407)Time elapsed: 0.090 s
% 0.21/0.54  % (16407)------------------------------
% 0.21/0.54  % (16407)------------------------------
% 0.21/0.54  % (16403)Success in time 0.181 s
%------------------------------------------------------------------------------
