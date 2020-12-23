%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  253 ( 533 expanded)
%              Number of leaves         :   51 ( 224 expanded)
%              Depth                    :   12
%              Number of atoms          : 1044 (2004 expanded)
%              Number of equality atoms :   99 ( 162 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f627,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f87,f91,f95,f99,f103,f111,f115,f119,f123,f198,f206,f218,f222,f226,f248,f257,f265,f266,f270,f290,f311,f329,f347,f373,f479,f483,f487,f556,f573,f608,f625,f626])).

fof(f626,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) != k1_funct_1(sK3,sK5)
    | k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f625,plain,
    ( spl6_71
    | spl6_3
    | ~ spl6_5
    | ~ spl6_37
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f614,f554,f485,f481,f327,f97,f89,f623])).

fof(f623,plain,
    ( spl6_71
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f89,plain,
    ( spl6_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f97,plain,
    ( spl6_5
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f327,plain,
    ( spl6_37
  <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f481,plain,
    ( spl6_53
  <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f485,plain,
    ( spl6_54
  <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f554,plain,
    ( spl6_60
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f614,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_3
    | ~ spl6_5
    | ~ spl6_37
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60 ),
    inference(forward_demodulation,[],[f613,f555])).

fof(f555,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f554])).

fof(f613,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_3
    | ~ spl6_5
    | ~ spl6_37
    | ~ spl6_53
    | ~ spl6_54 ),
    inference(resolution,[],[f509,f98])).

fof(f98,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f509,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1) )
    | spl6_3
    | ~ spl6_37
    | ~ spl6_53
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f508,f90])).

fof(f90,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f508,plain,
    ( ! [X1] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1) )
    | ~ spl6_37
    | ~ spl6_53
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f507,f482])).

fof(f482,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f481])).

fof(f507,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1) )
    | ~ spl6_37
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f489,f328])).

fof(f328,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f327])).

fof(f489,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
        | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1) )
    | ~ spl6_54 ),
    inference(resolution,[],[f486,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f486,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f485])).

fof(f608,plain,
    ( spl6_68
    | ~ spl6_1
    | spl6_4
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f314,f309,f117,f101,f93,f81,f606])).

fof(f606,plain,
    ( spl6_68
  <=> k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f81,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f93,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f101,plain,
    ( spl6_6
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f117,plain,
    ( spl6_9
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f309,plain,
    ( spl6_35
  <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f314,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | spl6_4
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_35 ),
    inference(resolution,[],[f310,f155])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f152,f154])).

fof(f154,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f153,f102])).

fof(f102,plain,
    ( v1_partfun1(sK4,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f153,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_partfun1(sK4,sK0)
    | spl6_4
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f130,f94])).

fof(f94,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f130,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_partfun1(sK4,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f118,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f118,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f152,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK2)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f140,f147])).

fof(f147,plain,
    ( v1_funct_2(sK4,sK0,sK2)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f146,f102])).

fof(f146,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | v1_funct_2(sK4,sK0,sK2)
    | ~ spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f129,f82])).

fof(f82,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f129,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_partfun1(sK4,sK0)
    | v1_funct_2(sK4,sK0,sK2)
    | ~ spl6_9 ),
    inference(resolution,[],[f118,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

% (19946)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f140,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK2)
        | ~ v1_funct_2(sK4,sK0,sK2)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f139,f94])).

fof(f139,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK2)
        | ~ v1_funct_2(sK4,sK0,sK2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f124,f82])).

fof(f124,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK2)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,sK0,sK2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_9 ),
    inference(resolution,[],[f118,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

fof(f310,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f309])).

fof(f573,plain,
    ( spl6_64
    | ~ spl6_1
    | spl6_4
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f315,f309,f117,f101,f93,f81,f571])).

fof(f571,plain,
    ( spl6_64
  <=> k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f315,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | spl6_4
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_35 ),
    inference(resolution,[],[f310,f151])).

fof(f151,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | k3_funct_2(sK0,sK2,sK4,X1) = k1_funct_1(sK4,X1) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f142,f147])).

fof(f142,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK4,sK0,sK2)
        | ~ m1_subset_1(X1,sK0)
        | k3_funct_2(sK0,sK2,sK4,X1) = k1_funct_1(sK4,X1) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f141,f94])).

fof(f141,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK4,sK0,sK2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,sK0)
        | k3_funct_2(sK0,sK2,sK4,X1) = k1_funct_1(sK4,X1) )
    | ~ spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f125,f82])).

fof(f125,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,sK0,sK2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,sK0)
        | k3_funct_2(sK0,sK2,sK4,X1) = k1_funct_1(sK4,X1) )
    | ~ spl6_9 ),
    inference(resolution,[],[f118,f58])).

fof(f556,plain,
    ( spl6_60
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_30
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f527,f345,f288,f263,f259,f121,f117,f113,f93,f85,f81,f554])).

fof(f85,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f113,plain,
    ( spl6_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f121,plain,
    ( spl6_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f259,plain,
    ( spl6_24
  <=> sK0 = k1_relset_1(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f263,plain,
    ( spl6_25
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f288,plain,
    ( spl6_30
  <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f345,plain,
    ( spl6_40
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))
        | ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f527,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_30
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f526,f82])).

fof(f526,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ v1_funct_1(sK4)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_30
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f525,f118])).

fof(f525,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_30
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f524,f264])).

fof(f264,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f263])).

fof(f524,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_40 ),
    inference(superposition,[],[f380,f260])).

fof(f260,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK4)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f259])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1) )
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_30
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f379,f114])).

fof(f114,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f379,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK3,sK1,sK0) )
    | ~ spl6_2
    | spl6_4
    | ~ spl6_10
    | ~ spl6_30
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f378,f122])).

fof(f122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f378,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(sK3,sK1,sK0) )
    | ~ spl6_2
    | spl6_4
    | ~ spl6_30
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f377,f94])).

fof(f377,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(sK3,sK1,sK0) )
    | ~ spl6_2
    | ~ spl6_30
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f374,f86])).

fof(f86,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f374,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(sK3,sK1,sK0) )
    | ~ spl6_30
    | ~ spl6_40 ),
    inference(superposition,[],[f346,f289])).

fof(f289,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f288])).

fof(f346,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))
        | ~ v1_funct_1(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f345])).

fof(f487,plain,
    ( spl6_54
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f337,f121,f117,f113,f85,f81,f485])).

fof(f337,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f336,f82])).

fof(f336,plain,
    ( ~ v1_funct_1(sK4)
    | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f186,f118])).

fof(f186,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,X7)))
        | ~ v1_funct_1(X6)
        | m1_subset_1(k8_funct_2(sK1,sK0,X7,sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f185,f86])).

fof(f185,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,X7)))
        | m1_subset_1(k8_funct_2(sK1,sK0,X7,sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) )
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f163,f114])).

fof(f163,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,X7)))
        | m1_subset_1(k8_funct_2(sK1,sK0,X7,sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) )
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f483,plain,
    ( spl6_53
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f331,f121,f117,f113,f85,f81,f481])).

fof(f331,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f330,f82])).

fof(f330,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f184,f118])).

fof(f184,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X5)))
        | ~ v1_funct_1(X4)
        | v1_funct_2(k8_funct_2(sK1,sK0,X5,sK3,X4),sK1,X5) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f183,f86])).

fof(f183,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X5)))
        | v1_funct_2(k8_funct_2(sK1,sK0,X5,sK3,X4),sK1,X5) )
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f162,f114])).

fof(f162,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X5)))
        | v1_funct_2(k8_funct_2(sK1,sK0,X5,sK3,X4),sK1,X5) )
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f479,plain,
    ( spl6_52
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f306,f121,f113,f97,f89,f85,f477])).

fof(f477,plain,
    ( spl6_52
  <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f306,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(resolution,[],[f180,f98])).

fof(f180,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1)
        | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f179,f90])).

fof(f179,plain,
    ( ! [X1] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1)
        | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f178,f114])).

fof(f178,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1)
        | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1) )
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f160,f86])).

fof(f160,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1)
        | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1) )
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f58])).

fof(f373,plain,
    ( spl6_3
    | ~ spl6_39 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | spl6_3
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f357,f67])).

fof(f67,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f357,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_39 ),
    inference(superposition,[],[f90,f343])).

fof(f343,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl6_39
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f347,plain,
    ( spl6_39
    | spl6_40
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f105,f97,f345,f342])).

fof(f105,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK1,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | v1_xboole_0(X1)
        | ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f98,f62])).

% (19940)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f329,plain,
    ( spl6_37
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f324,f121,f117,f113,f85,f81,f327])).

fof(f324,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f323,f82])).

fof(f323,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f182,f118])).

fof(f182,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
        | ~ v1_funct_1(X2)
        | v1_funct_1(k8_funct_2(sK1,sK0,X3,sK3,X2)) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f181,f86])).

fof(f181,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
        | v1_funct_1(k8_funct_2(sK1,sK0,X3,sK3,X2)) )
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f161,f114])).

fof(f161,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
        | v1_funct_1(k8_funct_2(sK1,sK0,X3,sK3,X2)) )
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f311,plain,
    ( spl6_35
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f307,f268,f220,f204,f109,f85,f309])).

fof(f109,plain,
    ( spl6_7
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f204,plain,
    ( spl6_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f220,plain,
    ( spl6_18
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f268,plain,
    ( spl6_26
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f307,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_26 ),
    inference(resolution,[],[f305,f110])).

fof(f110,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f305,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | m1_subset_1(k1_funct_1(sK3,X0),sK0) )
    | ~ spl6_2
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_26 ),
    inference(superposition,[],[f237,f269])).

fof(f269,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f268])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X0),sK0) )
    | ~ spl6_2
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f236,f86])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X0),sK0) )
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f234,f205])).

fof(f205,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f204])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X0),sK0) )
    | ~ spl6_18 ),
    inference(resolution,[],[f221,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | m1_subset_1(k1_funct_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(f221,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f220])).

fof(f290,plain,
    ( spl6_30
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f168,f121,f288])).

% (19944)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f168,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f270,plain,
    ( spl6_26
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f240,f224,f216,f204,f268])).

fof(f216,plain,
    ( spl6_17
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f224,plain,
    ( spl6_19
  <=> v1_partfun1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f240,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f239,f205])).

fof(f239,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f238,f217])).

fof(f217,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f216])).

fof(f238,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | sK1 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_19 ),
    inference(resolution,[],[f225,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f225,plain,
    ( v1_partfun1(sK3,sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f224])).

fof(f266,plain,
    ( spl6_24
    | ~ spl6_21
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f261,f255,f246,f259])).

fof(f246,plain,
    ( spl6_21
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f255,plain,
    ( spl6_23
  <=> k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f261,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK4)
    | ~ spl6_21
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f256,f247])).

fof(f247,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f246])).

fof(f256,plain,
    ( k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f255])).

fof(f265,plain,
    ( spl6_25
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f235,f220,f204,f263])).

fof(f235,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f233,f205])).

fof(f233,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_18 ),
    inference(resolution,[],[f221,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f257,plain,
    ( spl6_23
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f132,f117,f255])).

fof(f132,plain,
    ( k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4)
    | ~ spl6_9 ),
    inference(resolution,[],[f118,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f248,plain,
    ( spl6_21
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f158,f117,f101,f246])).

fof(f158,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f156,f157])).

fof(f157,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f136,f77])).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f136,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK4)
    | ~ spl6_9 ),
    inference(resolution,[],[f118,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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

fof(f156,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f107,f134])).

fof(f134,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f118,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f107,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | sK0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_6 ),
    inference(resolution,[],[f102,f74])).

fof(f226,plain,
    ( spl6_19
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f189,f121,f113,f93,f85,f224])).

fof(f189,plain,
    ( v1_partfun1(sK3,sK1)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f188,f114])).

fof(f188,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | v1_partfun1(sK3,sK1)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f187,f86])).

fof(f187,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | v1_partfun1(sK3,sK1)
    | spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f166,f94])).

fof(f166,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | v1_partfun1(sK3,sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f222,plain,
    ( spl6_18
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f170,f121,f220])).

fof(f170,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f218,plain,
    ( spl6_17
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f169,f121,f216])).

fof(f169,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f75])).

fof(f206,plain,
    ( spl6_14
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f190,f121,f204])).

fof(f190,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f171,f77])).

fof(f171,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f78])).

fof(f198,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f49,f196])).

fof(f196,plain,
    ( spl6_12
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f49,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

fof(f123,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f54,f121])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f119,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f51,f117])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f115,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f53,f113])).

fof(f53,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f111,plain,
    ( spl6_7
    | spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f106,f97,f89,f109])).

fof(f106,plain,
    ( r2_hidden(sK5,sK1)
    | spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f104,f90])).

fof(f104,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK5,sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f98,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f103,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f99,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f47,f97])).

fof(f47,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f95,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f56,f93])).

fof(f56,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f55,f89])).

fof(f55,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f52,f85])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f50,f81])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (19942)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (19936)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (19934)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (19929)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (19932)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (19935)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (19938)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (19933)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (19937)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (19931)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (19929)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (19945)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (19941)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (19930)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (19947)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (19930)Refutation not found, incomplete strategy% (19930)------------------------------
% 0.21/0.51  % (19930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19930)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19930)Memory used [KB]: 10618
% 0.21/0.51  % (19930)Time elapsed: 0.094 s
% 0.21/0.51  % (19930)------------------------------
% 0.21/0.51  % (19930)------------------------------
% 0.21/0.51  % (19949)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (19943)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (19939)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (19949)Refutation not found, incomplete strategy% (19949)------------------------------
% 0.21/0.51  % (19949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19949)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19949)Memory used [KB]: 10618
% 0.21/0.51  % (19949)Time elapsed: 0.106 s
% 0.21/0.51  % (19949)------------------------------
% 0.21/0.51  % (19949)------------------------------
% 1.34/0.52  % SZS output start Proof for theBenchmark
% 1.34/0.52  fof(f627,plain,(
% 1.34/0.52    $false),
% 1.34/0.52    inference(avatar_sat_refutation,[],[f83,f87,f91,f95,f99,f103,f111,f115,f119,f123,f198,f206,f218,f222,f226,f248,f257,f265,f266,f270,f290,f311,f329,f347,f373,f479,f483,f487,f556,f573,f608,f625,f626])).
% 1.34/0.52  fof(f626,plain,(
% 1.34/0.52    k3_funct_2(sK1,sK0,sK3,sK5) != k1_funct_1(sK3,sK5) | k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 1.34/0.52    introduced(theory_tautology_sat_conflict,[])).
% 1.34/0.52  fof(f625,plain,(
% 1.34/0.52    spl6_71 | spl6_3 | ~spl6_5 | ~spl6_37 | ~spl6_53 | ~spl6_54 | ~spl6_60),
% 1.34/0.52    inference(avatar_split_clause,[],[f614,f554,f485,f481,f327,f97,f89,f623])).
% 1.34/0.52  fof(f623,plain,(
% 1.34/0.52    spl6_71 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 1.34/0.52  fof(f89,plain,(
% 1.34/0.52    spl6_3 <=> v1_xboole_0(sK1)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.34/0.52  fof(f97,plain,(
% 1.34/0.52    spl6_5 <=> m1_subset_1(sK5,sK1)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.34/0.52  fof(f327,plain,(
% 1.34/0.52    spl6_37 <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.34/0.52  fof(f481,plain,(
% 1.34/0.52    spl6_53 <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 1.34/0.52  fof(f485,plain,(
% 1.34/0.52    spl6_54 <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 1.34/0.52  fof(f554,plain,(
% 1.34/0.52    spl6_60 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 1.34/0.52  fof(f614,plain,(
% 1.34/0.52    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_3 | ~spl6_5 | ~spl6_37 | ~spl6_53 | ~spl6_54 | ~spl6_60)),
% 1.34/0.52    inference(forward_demodulation,[],[f613,f555])).
% 1.34/0.52  fof(f555,plain,(
% 1.34/0.52    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~spl6_60),
% 1.34/0.52    inference(avatar_component_clause,[],[f554])).
% 1.34/0.52  fof(f613,plain,(
% 1.34/0.52    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | (spl6_3 | ~spl6_5 | ~spl6_37 | ~spl6_53 | ~spl6_54)),
% 1.34/0.52    inference(resolution,[],[f509,f98])).
% 1.34/0.52  fof(f98,plain,(
% 1.34/0.52    m1_subset_1(sK5,sK1) | ~spl6_5),
% 1.34/0.52    inference(avatar_component_clause,[],[f97])).
% 1.34/0.52  fof(f509,plain,(
% 1.34/0.52    ( ! [X1] : (~m1_subset_1(X1,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1)) ) | (spl6_3 | ~spl6_37 | ~spl6_53 | ~spl6_54)),
% 1.34/0.52    inference(subsumption_resolution,[],[f508,f90])).
% 1.34/0.52  fof(f90,plain,(
% 1.34/0.52    ~v1_xboole_0(sK1) | spl6_3),
% 1.34/0.52    inference(avatar_component_clause,[],[f89])).
% 1.34/0.52  fof(f508,plain,(
% 1.34/0.52    ( ! [X1] : (v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1)) ) | (~spl6_37 | ~spl6_53 | ~spl6_54)),
% 1.34/0.52    inference(subsumption_resolution,[],[f507,f482])).
% 1.34/0.52  fof(f482,plain,(
% 1.34/0.52    v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~spl6_53),
% 1.34/0.52    inference(avatar_component_clause,[],[f481])).
% 1.34/0.52  fof(f507,plain,(
% 1.34/0.52    ( ! [X1] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1)) ) | (~spl6_37 | ~spl6_54)),
% 1.34/0.52    inference(subsumption_resolution,[],[f489,f328])).
% 1.34/0.52  fof(f328,plain,(
% 1.34/0.52    v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~spl6_37),
% 1.34/0.52    inference(avatar_component_clause,[],[f327])).
% 1.34/0.52  fof(f489,plain,(
% 1.34/0.52    ( ! [X1] : (~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X1)) ) | ~spl6_54),
% 1.34/0.52    inference(resolution,[],[f486,f58])).
% 1.34/0.52  fof(f58,plain,(
% 1.34/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 1.34/0.52    inference(cnf_transformation,[],[f25])).
% 1.34/0.52  fof(f25,plain,(
% 1.34/0.52    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.34/0.52    inference(flattening,[],[f24])).
% 1.34/0.52  fof(f24,plain,(
% 1.34/0.52    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.34/0.52    inference(ennf_transformation,[],[f15])).
% 1.34/0.52  fof(f15,axiom,(
% 1.34/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.34/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.34/0.52  fof(f486,plain,(
% 1.34/0.52    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_54),
% 1.34/0.52    inference(avatar_component_clause,[],[f485])).
% 1.34/0.52  fof(f608,plain,(
% 1.34/0.52    spl6_68 | ~spl6_1 | spl6_4 | ~spl6_6 | ~spl6_9 | ~spl6_35),
% 1.34/0.52    inference(avatar_split_clause,[],[f314,f309,f117,f101,f93,f81,f606])).
% 1.34/0.52  fof(f606,plain,(
% 1.34/0.52    spl6_68 <=> k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 1.34/0.52  fof(f81,plain,(
% 1.34/0.52    spl6_1 <=> v1_funct_1(sK4)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.34/0.52  fof(f93,plain,(
% 1.34/0.52    spl6_4 <=> v1_xboole_0(sK0)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.34/0.52  fof(f101,plain,(
% 1.34/0.52    spl6_6 <=> v1_partfun1(sK4,sK0)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.34/0.52  fof(f117,plain,(
% 1.34/0.52    spl6_9 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.34/0.52  fof(f309,plain,(
% 1.34/0.52    spl6_35 <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.34/0.52  fof(f314,plain,(
% 1.34/0.52    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | spl6_4 | ~spl6_6 | ~spl6_9 | ~spl6_35)),
% 1.34/0.52    inference(resolution,[],[f310,f155])).
% 1.34/0.52  fof(f155,plain,(
% 1.34/0.52    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | (~spl6_1 | spl6_4 | ~spl6_6 | ~spl6_9)),
% 1.34/0.52    inference(subsumption_resolution,[],[f152,f154])).
% 1.34/0.52  fof(f154,plain,(
% 1.34/0.52    ~v1_xboole_0(sK2) | (spl6_4 | ~spl6_6 | ~spl6_9)),
% 1.34/0.52    inference(subsumption_resolution,[],[f153,f102])).
% 1.34/0.52  fof(f102,plain,(
% 1.34/0.52    v1_partfun1(sK4,sK0) | ~spl6_6),
% 1.34/0.52    inference(avatar_component_clause,[],[f101])).
% 1.34/0.52  fof(f153,plain,(
% 1.34/0.52    ~v1_xboole_0(sK2) | ~v1_partfun1(sK4,sK0) | (spl6_4 | ~spl6_9)),
% 1.34/0.52    inference(subsumption_resolution,[],[f130,f94])).
% 1.34/0.52  fof(f94,plain,(
% 1.34/0.52    ~v1_xboole_0(sK0) | spl6_4),
% 1.34/0.52    inference(avatar_component_clause,[],[f93])).
% 1.34/0.52  fof(f130,plain,(
% 1.34/0.52    ~v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~v1_partfun1(sK4,sK0) | ~spl6_9),
% 1.34/0.52    inference(resolution,[],[f118,f64])).
% 1.34/0.52  fof(f64,plain,(
% 1.34/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_partfun1(X2,X0)) )),
% 1.34/0.52    inference(cnf_transformation,[],[f33])).
% 1.34/0.52  fof(f33,plain,(
% 1.34/0.52    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.34/0.52    inference(flattening,[],[f32])).
% 1.34/0.52  fof(f32,plain,(
% 1.34/0.52    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.34/0.52    inference(ennf_transformation,[],[f11])).
% 1.34/0.52  fof(f11,axiom,(
% 1.34/0.52    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 1.34/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).
% 1.34/0.52  fof(f118,plain,(
% 1.34/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_9),
% 1.34/0.52    inference(avatar_component_clause,[],[f117])).
% 1.34/0.52  fof(f152,plain,(
% 1.34/0.52    ( ! [X0] : (v1_xboole_0(sK2) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | (~spl6_1 | spl6_4 | ~spl6_6 | ~spl6_9)),
% 1.34/0.52    inference(subsumption_resolution,[],[f140,f147])).
% 1.34/0.52  fof(f147,plain,(
% 1.34/0.52    v1_funct_2(sK4,sK0,sK2) | (~spl6_1 | ~spl6_6 | ~spl6_9)),
% 1.34/0.52    inference(subsumption_resolution,[],[f146,f102])).
% 1.34/0.52  fof(f146,plain,(
% 1.34/0.52    ~v1_partfun1(sK4,sK0) | v1_funct_2(sK4,sK0,sK2) | (~spl6_1 | ~spl6_9)),
% 1.34/0.52    inference(subsumption_resolution,[],[f129,f82])).
% 1.34/0.52  fof(f82,plain,(
% 1.34/0.52    v1_funct_1(sK4) | ~spl6_1),
% 1.34/0.52    inference(avatar_component_clause,[],[f81])).
% 1.34/0.52  fof(f129,plain,(
% 1.34/0.52    ~v1_funct_1(sK4) | ~v1_partfun1(sK4,sK0) | v1_funct_2(sK4,sK0,sK2) | ~spl6_9),
% 1.34/0.52    inference(resolution,[],[f118,f63])).
% 1.34/0.52  fof(f63,plain,(
% 1.34/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 1.34/0.52    inference(cnf_transformation,[],[f31])).
% 1.34/0.52  % (19946)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.34/0.52  fof(f31,plain,(
% 1.34/0.52    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.52    inference(flattening,[],[f30])).
% 1.34/0.52  fof(f30,plain,(
% 1.34/0.52    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.52    inference(ennf_transformation,[],[f10])).
% 1.34/0.52  fof(f10,axiom,(
% 1.34/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.34/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 1.34/0.52  fof(f140,plain,(
% 1.34/0.52    ( ! [X0] : (v1_xboole_0(sK2) | ~v1_funct_2(sK4,sK0,sK2) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | (~spl6_1 | spl6_4 | ~spl6_9)),
% 1.34/0.52    inference(subsumption_resolution,[],[f139,f94])).
% 1.34/0.52  fof(f139,plain,(
% 1.34/0.52    ( ! [X0] : (v1_xboole_0(sK2) | ~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | (~spl6_1 | ~spl6_9)),
% 1.34/0.52    inference(subsumption_resolution,[],[f124,f82])).
% 1.34/0.52  fof(f124,plain,(
% 1.34/0.52    ( ! [X0] : (v1_xboole_0(sK2) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | ~spl6_9),
% 1.34/0.52    inference(resolution,[],[f118,f57])).
% 1.34/0.52  fof(f57,plain,(
% 1.34/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)) )),
% 1.34/0.52    inference(cnf_transformation,[],[f23])).
% 1.34/0.52  fof(f23,plain,(
% 1.34/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.34/0.52    inference(flattening,[],[f22])).
% 1.34/0.52  fof(f22,plain,(
% 1.34/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.34/0.52    inference(ennf_transformation,[],[f16])).
% 1.34/0.52  fof(f16,axiom,(
% 1.34/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 1.34/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).
% 1.34/0.52  fof(f310,plain,(
% 1.34/0.52    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~spl6_35),
% 1.34/0.52    inference(avatar_component_clause,[],[f309])).
% 1.34/0.52  fof(f573,plain,(
% 1.34/0.52    spl6_64 | ~spl6_1 | spl6_4 | ~spl6_6 | ~spl6_9 | ~spl6_35),
% 1.34/0.52    inference(avatar_split_clause,[],[f315,f309,f117,f101,f93,f81,f571])).
% 1.34/0.52  fof(f571,plain,(
% 1.34/0.52    spl6_64 <=> k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 1.34/0.52  fof(f315,plain,(
% 1.34/0.52    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | spl6_4 | ~spl6_6 | ~spl6_9 | ~spl6_35)),
% 1.34/0.52    inference(resolution,[],[f310,f151])).
% 1.34/0.52  fof(f151,plain,(
% 1.34/0.52    ( ! [X1] : (~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK2,sK4,X1) = k1_funct_1(sK4,X1)) ) | (~spl6_1 | spl6_4 | ~spl6_6 | ~spl6_9)),
% 1.34/0.52    inference(subsumption_resolution,[],[f142,f147])).
% 1.34/0.52  fof(f142,plain,(
% 1.34/0.52    ( ! [X1] : (~v1_funct_2(sK4,sK0,sK2) | ~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK2,sK4,X1) = k1_funct_1(sK4,X1)) ) | (~spl6_1 | spl6_4 | ~spl6_9)),
% 1.34/0.52    inference(subsumption_resolution,[],[f141,f94])).
% 1.34/0.52  fof(f141,plain,(
% 1.34/0.52    ( ! [X1] : (~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK2,sK4,X1) = k1_funct_1(sK4,X1)) ) | (~spl6_1 | ~spl6_9)),
% 1.34/0.52    inference(subsumption_resolution,[],[f125,f82])).
% 1.34/0.52  fof(f125,plain,(
% 1.34/0.52    ( ! [X1] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK2,sK4,X1) = k1_funct_1(sK4,X1)) ) | ~spl6_9),
% 1.34/0.52    inference(resolution,[],[f118,f58])).
% 1.34/0.52  fof(f556,plain,(
% 1.34/0.52    spl6_60 | ~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_24 | ~spl6_25 | ~spl6_30 | ~spl6_40),
% 1.34/0.52    inference(avatar_split_clause,[],[f527,f345,f288,f263,f259,f121,f117,f113,f93,f85,f81,f554])).
% 1.34/0.52  fof(f85,plain,(
% 1.34/0.52    spl6_2 <=> v1_funct_1(sK3)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.34/0.52  fof(f113,plain,(
% 1.34/0.52    spl6_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.34/0.52  fof(f121,plain,(
% 1.34/0.52    spl6_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.34/0.52  fof(f259,plain,(
% 1.34/0.52    spl6_24 <=> sK0 = k1_relset_1(sK0,sK2,sK4)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.34/0.52  fof(f263,plain,(
% 1.34/0.52    spl6_25 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.34/0.52  fof(f288,plain,(
% 1.34/0.52    spl6_30 <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.34/0.52  fof(f345,plain,(
% 1.34/0.52    spl6_40 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X0) | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) | ~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.34/0.52  fof(f527,plain,(
% 1.34/0.52    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_24 | ~spl6_25 | ~spl6_30 | ~spl6_40)),
% 1.34/0.52    inference(subsumption_resolution,[],[f526,f82])).
% 1.34/0.52  fof(f526,plain,(
% 1.34/0.52    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~v1_funct_1(sK4) | (~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_24 | ~spl6_25 | ~spl6_30 | ~spl6_40)),
% 1.34/0.52    inference(subsumption_resolution,[],[f525,f118])).
% 1.34/0.52  fof(f525,plain,(
% 1.34/0.52    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | (~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_10 | ~spl6_24 | ~spl6_25 | ~spl6_30 | ~spl6_40)),
% 1.34/0.52    inference(subsumption_resolution,[],[f524,f264])).
% 1.34/0.52  fof(f264,plain,(
% 1.34/0.52    r1_tarski(k2_relat_1(sK3),sK0) | ~spl6_25),
% 1.34/0.52    inference(avatar_component_clause,[],[f263])).
% 1.34/0.52  fof(f524,plain,(
% 1.34/0.52    ~r1_tarski(k2_relat_1(sK3),sK0) | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | (~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_10 | ~spl6_24 | ~spl6_30 | ~spl6_40)),
% 1.34/0.52    inference(superposition,[],[f380,f260])).
% 1.34/0.52  fof(f260,plain,(
% 1.34/0.52    sK0 = k1_relset_1(sK0,sK2,sK4) | ~spl6_24),
% 1.34/0.52    inference(avatar_component_clause,[],[f259])).
% 1.34/0.52  fof(f380,plain,(
% 1.34/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1)) ) | (~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_10 | ~spl6_30 | ~spl6_40)),
% 1.34/0.52    inference(subsumption_resolution,[],[f379,f114])).
% 1.34/0.52  fof(f114,plain,(
% 1.34/0.52    v1_funct_2(sK3,sK1,sK0) | ~spl6_8),
% 1.34/0.52    inference(avatar_component_clause,[],[f113])).
% 1.34/0.52  fof(f379,plain,(
% 1.34/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~v1_funct_2(sK3,sK1,sK0)) ) | (~spl6_2 | spl6_4 | ~spl6_10 | ~spl6_30 | ~spl6_40)),
% 1.34/0.52    inference(subsumption_resolution,[],[f378,f122])).
% 1.34/0.52  fof(f122,plain,(
% 1.34/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_10),
% 1.34/0.52    inference(avatar_component_clause,[],[f121])).
% 1.34/0.52  fof(f378,plain,(
% 1.34/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0)) ) | (~spl6_2 | spl6_4 | ~spl6_30 | ~spl6_40)),
% 1.34/0.52    inference(subsumption_resolution,[],[f377,f94])).
% 1.34/0.52  fof(f377,plain,(
% 1.34/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) | v1_xboole_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0)) ) | (~spl6_2 | ~spl6_30 | ~spl6_40)),
% 1.34/0.52    inference(subsumption_resolution,[],[f374,f86])).
% 1.34/0.52  fof(f86,plain,(
% 1.34/0.52    v1_funct_1(sK3) | ~spl6_2),
% 1.34/0.52    inference(avatar_component_clause,[],[f85])).
% 1.34/0.52  fof(f374,plain,(
% 1.34/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0)) ) | (~spl6_30 | ~spl6_40)),
% 1.34/0.52    inference(superposition,[],[f346,f289])).
% 1.34/0.52  fof(f289,plain,(
% 1.34/0.52    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) | ~spl6_30),
% 1.34/0.52    inference(avatar_component_clause,[],[f288])).
% 1.34/0.52  fof(f346,plain,(
% 1.34/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) | ~v1_funct_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl6_40),
% 1.34/0.52    inference(avatar_component_clause,[],[f345])).
% 1.34/0.52  fof(f487,plain,(
% 1.34/0.52    spl6_54 | ~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_10),
% 1.34/0.52    inference(avatar_split_clause,[],[f337,f121,f117,f113,f85,f81,f485])).
% 1.34/0.52  fof(f337,plain,(
% 1.34/0.52    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.34/0.52    inference(subsumption_resolution,[],[f336,f82])).
% 1.34/0.52  fof(f336,plain,(
% 1.34/0.52    ~v1_funct_1(sK4) | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.34/0.52    inference(resolution,[],[f186,f118])).
% 1.34/0.52  fof(f186,plain,(
% 1.34/0.52    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,X7))) | ~v1_funct_1(X6) | m1_subset_1(k8_funct_2(sK1,sK0,X7,sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))) ) | (~spl6_2 | ~spl6_8 | ~spl6_10)),
% 1.34/0.52    inference(subsumption_resolution,[],[f185,f86])).
% 1.34/0.52  fof(f185,plain,(
% 1.34/0.52    ( ! [X6,X7] : (~v1_funct_1(sK3) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,X7))) | m1_subset_1(k8_funct_2(sK1,sK0,X7,sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))) ) | (~spl6_8 | ~spl6_10)),
% 1.34/0.52    inference(subsumption_resolution,[],[f163,f114])).
% 1.34/0.52  fof(f163,plain,(
% 1.34/0.52    ( ! [X6,X7] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,X7))) | m1_subset_1(k8_funct_2(sK1,sK0,X7,sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))) ) | ~spl6_10),
% 1.34/0.52    inference(resolution,[],[f122,f61])).
% 1.34/0.52  fof(f61,plain,(
% 1.34/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 1.34/0.52    inference(cnf_transformation,[],[f27])).
% 1.34/0.52  fof(f27,plain,(
% 1.34/0.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.34/0.52    inference(flattening,[],[f26])).
% 1.34/0.52  fof(f26,plain,(
% 1.34/0.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.34/0.52    inference(ennf_transformation,[],[f14])).
% 1.34/0.52  fof(f14,axiom,(
% 1.34/0.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 1.34/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).
% 1.34/0.52  fof(f483,plain,(
% 1.34/0.52    spl6_53 | ~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_10),
% 1.34/0.52    inference(avatar_split_clause,[],[f331,f121,f117,f113,f85,f81,f481])).
% 1.34/0.52  fof(f331,plain,(
% 1.34/0.52    v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.34/0.52    inference(subsumption_resolution,[],[f330,f82])).
% 1.34/0.52  fof(f330,plain,(
% 1.34/0.52    ~v1_funct_1(sK4) | v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | (~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.34/0.52    inference(resolution,[],[f184,f118])).
% 1.34/0.52  fof(f184,plain,(
% 1.34/0.52    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) | ~v1_funct_1(X4) | v1_funct_2(k8_funct_2(sK1,sK0,X5,sK3,X4),sK1,X5)) ) | (~spl6_2 | ~spl6_8 | ~spl6_10)),
% 1.34/0.52    inference(subsumption_resolution,[],[f183,f86])).
% 1.34/0.52  fof(f183,plain,(
% 1.34/0.52    ( ! [X4,X5] : (~v1_funct_1(sK3) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) | v1_funct_2(k8_funct_2(sK1,sK0,X5,sK3,X4),sK1,X5)) ) | (~spl6_8 | ~spl6_10)),
% 1.34/0.52    inference(subsumption_resolution,[],[f162,f114])).
% 1.34/0.52  fof(f162,plain,(
% 1.34/0.52    ( ! [X4,X5] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) | v1_funct_2(k8_funct_2(sK1,sK0,X5,sK3,X4),sK1,X5)) ) | ~spl6_10),
% 1.34/0.52    inference(resolution,[],[f122,f60])).
% 1.34/0.52  fof(f60,plain,(
% 1.34/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)) )),
% 1.34/0.52    inference(cnf_transformation,[],[f27])).
% 1.34/0.52  fof(f479,plain,(
% 1.34/0.52    spl6_52 | ~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10),
% 1.34/0.52    inference(avatar_split_clause,[],[f306,f121,f113,f97,f89,f85,f477])).
% 1.34/0.52  fof(f477,plain,(
% 1.34/0.52    spl6_52 <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 1.34/0.52  fof(f306,plain,(
% 1.34/0.52    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | (~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10)),
% 1.34/0.52    inference(resolution,[],[f180,f98])).
% 1.34/0.52  fof(f180,plain,(
% 1.34/0.52    ( ! [X1] : (~m1_subset_1(X1,sK1) | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1)) ) | (~spl6_2 | spl6_3 | ~spl6_8 | ~spl6_10)),
% 1.34/0.52    inference(subsumption_resolution,[],[f179,f90])).
% 1.34/0.52  fof(f179,plain,(
% 1.34/0.52    ( ! [X1] : (v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1) | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1)) ) | (~spl6_2 | ~spl6_8 | ~spl6_10)),
% 1.34/0.52    inference(subsumption_resolution,[],[f178,f114])).
% 1.34/0.52  fof(f178,plain,(
% 1.34/0.52    ( ! [X1] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1) | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1)) ) | (~spl6_2 | ~spl6_10)),
% 1.34/0.52    inference(subsumption_resolution,[],[f160,f86])).
% 1.34/0.52  fof(f160,plain,(
% 1.34/0.52    ( ! [X1] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1) | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1)) ) | ~spl6_10),
% 1.34/0.52    inference(resolution,[],[f122,f58])).
% 1.34/0.52  fof(f373,plain,(
% 1.34/0.52    spl6_3 | ~spl6_39),
% 1.34/0.52    inference(avatar_contradiction_clause,[],[f372])).
% 1.34/0.52  fof(f372,plain,(
% 1.34/0.52    $false | (spl6_3 | ~spl6_39)),
% 1.34/0.52    inference(subsumption_resolution,[],[f357,f67])).
% 1.34/0.52  fof(f67,plain,(
% 1.34/0.52    v1_xboole_0(k1_xboole_0)),
% 1.34/0.52    inference(cnf_transformation,[],[f1])).
% 1.34/0.52  fof(f1,axiom,(
% 1.34/0.52    v1_xboole_0(k1_xboole_0)),
% 1.34/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.34/0.52  fof(f357,plain,(
% 1.34/0.52    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_39)),
% 1.34/0.52    inference(superposition,[],[f90,f343])).
% 1.34/0.52  fof(f343,plain,(
% 1.34/0.52    k1_xboole_0 = sK1 | ~spl6_39),
% 1.34/0.52    inference(avatar_component_clause,[],[f342])).
% 1.34/0.52  fof(f342,plain,(
% 1.34/0.52    spl6_39 <=> k1_xboole_0 = sK1),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.34/0.52  fof(f347,plain,(
% 1.34/0.52    spl6_39 | spl6_40 | ~spl6_5),
% 1.34/0.52    inference(avatar_split_clause,[],[f105,f97,f345,f342])).
% 1.34/0.52  fof(f105,plain,(
% 1.34/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(X1) | ~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))) ) | ~spl6_5),
% 1.34/0.52    inference(resolution,[],[f98,f62])).
% 1.34/0.52  % (19940)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.34/0.52  fof(f62,plain,(
% 1.34/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 1.34/0.52    inference(cnf_transformation,[],[f29])).
% 1.34/0.52  fof(f29,plain,(
% 1.34/0.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 1.34/0.52    inference(flattening,[],[f28])).
% 1.34/0.52  fof(f28,plain,(
% 1.34/0.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 1.34/0.52    inference(ennf_transformation,[],[f17])).
% 1.34/0.52  fof(f17,axiom,(
% 1.34/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.34/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 1.34/0.52  fof(f329,plain,(
% 1.34/0.52    spl6_37 | ~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_10),
% 1.34/0.52    inference(avatar_split_clause,[],[f324,f121,f117,f113,f85,f81,f327])).
% 1.34/0.52  fof(f324,plain,(
% 1.34/0.52    v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.34/0.52    inference(subsumption_resolution,[],[f323,f82])).
% 1.34/0.52  fof(f323,plain,(
% 1.34/0.52    ~v1_funct_1(sK4) | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | (~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.34/0.52    inference(resolution,[],[f182,f118])).
% 1.34/0.52  fof(f182,plain,(
% 1.34/0.52    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X3))) | ~v1_funct_1(X2) | v1_funct_1(k8_funct_2(sK1,sK0,X3,sK3,X2))) ) | (~spl6_2 | ~spl6_8 | ~spl6_10)),
% 1.34/0.52    inference(subsumption_resolution,[],[f181,f86])).
% 1.34/0.52  fof(f181,plain,(
% 1.34/0.52    ( ! [X2,X3] : (~v1_funct_1(sK3) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X3))) | v1_funct_1(k8_funct_2(sK1,sK0,X3,sK3,X2))) ) | (~spl6_8 | ~spl6_10)),
% 1.34/0.52    inference(subsumption_resolution,[],[f161,f114])).
% 1.34/0.52  fof(f161,plain,(
% 1.34/0.52    ( ! [X2,X3] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X3))) | v1_funct_1(k8_funct_2(sK1,sK0,X3,sK3,X2))) ) | ~spl6_10),
% 1.34/0.52    inference(resolution,[],[f122,f59])).
% 1.34/0.52  fof(f59,plain,(
% 1.34/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) )),
% 1.34/0.52    inference(cnf_transformation,[],[f27])).
% 1.34/0.52  fof(f311,plain,(
% 1.34/0.52    spl6_35 | ~spl6_2 | ~spl6_7 | ~spl6_14 | ~spl6_18 | ~spl6_26),
% 1.34/0.52    inference(avatar_split_clause,[],[f307,f268,f220,f204,f109,f85,f309])).
% 1.34/0.52  fof(f109,plain,(
% 1.34/0.52    spl6_7 <=> r2_hidden(sK5,sK1)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.34/0.52  fof(f204,plain,(
% 1.34/0.52    spl6_14 <=> v1_relat_1(sK3)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.34/0.52  fof(f220,plain,(
% 1.34/0.52    spl6_18 <=> v5_relat_1(sK3,sK0)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.34/0.52  fof(f268,plain,(
% 1.34/0.52    spl6_26 <=> sK1 = k1_relat_1(sK3)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.34/0.52  fof(f307,plain,(
% 1.34/0.52    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | (~spl6_2 | ~spl6_7 | ~spl6_14 | ~spl6_18 | ~spl6_26)),
% 1.34/0.52    inference(resolution,[],[f305,f110])).
% 1.34/0.52  fof(f110,plain,(
% 1.34/0.52    r2_hidden(sK5,sK1) | ~spl6_7),
% 1.34/0.52    inference(avatar_component_clause,[],[f109])).
% 1.34/0.52  fof(f305,plain,(
% 1.34/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | m1_subset_1(k1_funct_1(sK3,X0),sK0)) ) | (~spl6_2 | ~spl6_14 | ~spl6_18 | ~spl6_26)),
% 1.34/0.52    inference(superposition,[],[f237,f269])).
% 1.34/0.52  fof(f269,plain,(
% 1.34/0.52    sK1 = k1_relat_1(sK3) | ~spl6_26),
% 1.34/0.52    inference(avatar_component_clause,[],[f268])).
% 1.34/0.52  fof(f237,plain,(
% 1.34/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),sK0)) ) | (~spl6_2 | ~spl6_14 | ~spl6_18)),
% 1.34/0.52    inference(subsumption_resolution,[],[f236,f86])).
% 1.34/0.52  fof(f236,plain,(
% 1.34/0.52    ( ! [X0] : (~v1_funct_1(sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),sK0)) ) | (~spl6_14 | ~spl6_18)),
% 1.34/0.52    inference(subsumption_resolution,[],[f234,f205])).
% 1.34/0.52  fof(f205,plain,(
% 1.34/0.52    v1_relat_1(sK3) | ~spl6_14),
% 1.34/0.52    inference(avatar_component_clause,[],[f204])).
% 1.34/0.52  fof(f234,plain,(
% 1.34/0.52    ( ! [X0] : (~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),sK0)) ) | ~spl6_18),
% 1.34/0.52    inference(resolution,[],[f221,f66])).
% 1.34/0.52  fof(f66,plain,(
% 1.34/0.52    ( ! [X2,X0,X1] : (~v5_relat_1(X2,X0) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | m1_subset_1(k1_funct_1(X2,X1),X0)) )),
% 1.34/0.52    inference(cnf_transformation,[],[f37])).
% 1.34/0.52  fof(f37,plain,(
% 1.34/0.52    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 1.34/0.52    inference(flattening,[],[f36])).
% 1.34/0.52  fof(f36,plain,(
% 1.34/0.52    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 1.34/0.52    inference(ennf_transformation,[],[f6])).
% 1.34/0.52  fof(f6,axiom,(
% 1.34/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 1.34/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).
% 1.34/0.52  fof(f221,plain,(
% 1.34/0.52    v5_relat_1(sK3,sK0) | ~spl6_18),
% 1.34/0.52    inference(avatar_component_clause,[],[f220])).
% 1.34/0.52  fof(f290,plain,(
% 1.34/0.52    spl6_30 | ~spl6_10),
% 1.34/0.52    inference(avatar_split_clause,[],[f168,f121,f288])).
% 1.34/0.52  % (19944)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.34/0.52  fof(f168,plain,(
% 1.34/0.52    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) | ~spl6_10),
% 1.34/0.52    inference(resolution,[],[f122,f71])).
% 1.34/0.52  fof(f71,plain,(
% 1.34/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.34/0.52    inference(cnf_transformation,[],[f40])).
% 1.34/0.52  fof(f40,plain,(
% 1.34/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.52    inference(ennf_transformation,[],[f9])).
% 1.34/0.52  fof(f9,axiom,(
% 1.34/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.34/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.34/0.52  fof(f270,plain,(
% 1.34/0.52    spl6_26 | ~spl6_14 | ~spl6_17 | ~spl6_19),
% 1.34/0.52    inference(avatar_split_clause,[],[f240,f224,f216,f204,f268])).
% 1.34/0.52  fof(f216,plain,(
% 1.34/0.52    spl6_17 <=> v4_relat_1(sK3,sK1)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.34/0.52  fof(f224,plain,(
% 1.34/0.52    spl6_19 <=> v1_partfun1(sK3,sK1)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.34/0.52  fof(f240,plain,(
% 1.34/0.52    sK1 = k1_relat_1(sK3) | (~spl6_14 | ~spl6_17 | ~spl6_19)),
% 1.34/0.52    inference(subsumption_resolution,[],[f239,f205])).
% 1.34/0.52  fof(f239,plain,(
% 1.34/0.52    sK1 = k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl6_17 | ~spl6_19)),
% 1.34/0.52    inference(subsumption_resolution,[],[f238,f217])).
% 1.34/0.52  fof(f217,plain,(
% 1.34/0.52    v4_relat_1(sK3,sK1) | ~spl6_17),
% 1.34/0.52    inference(avatar_component_clause,[],[f216])).
% 1.34/0.52  fof(f238,plain,(
% 1.34/0.52    ~v4_relat_1(sK3,sK1) | sK1 = k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl6_19),
% 1.34/0.52    inference(resolution,[],[f225,f74])).
% 1.34/0.52  fof(f74,plain,(
% 1.34/0.52    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.34/0.52    inference(cnf_transformation,[],[f44])).
% 1.34/0.52  fof(f44,plain,(
% 1.34/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.52    inference(flattening,[],[f43])).
% 1.34/0.52  fof(f43,plain,(
% 1.34/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.34/0.52    inference(ennf_transformation,[],[f13])).
% 1.34/0.52  fof(f13,axiom,(
% 1.34/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.34/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 1.34/0.52  fof(f225,plain,(
% 1.34/0.52    v1_partfun1(sK3,sK1) | ~spl6_19),
% 1.34/0.52    inference(avatar_component_clause,[],[f224])).
% 1.34/0.52  fof(f266,plain,(
% 1.34/0.52    spl6_24 | ~spl6_21 | ~spl6_23),
% 1.34/0.52    inference(avatar_split_clause,[],[f261,f255,f246,f259])).
% 1.34/0.52  fof(f246,plain,(
% 1.34/0.52    spl6_21 <=> sK0 = k1_relat_1(sK4)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.34/0.52  fof(f255,plain,(
% 1.34/0.52    spl6_23 <=> k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.34/0.53  fof(f261,plain,(
% 1.34/0.53    sK0 = k1_relset_1(sK0,sK2,sK4) | (~spl6_21 | ~spl6_23)),
% 1.34/0.53    inference(forward_demodulation,[],[f256,f247])).
% 1.34/0.53  fof(f247,plain,(
% 1.34/0.53    sK0 = k1_relat_1(sK4) | ~spl6_21),
% 1.34/0.53    inference(avatar_component_clause,[],[f246])).
% 1.34/0.53  fof(f256,plain,(
% 1.34/0.53    k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4) | ~spl6_23),
% 1.34/0.53    inference(avatar_component_clause,[],[f255])).
% 1.34/0.53  fof(f265,plain,(
% 1.34/0.53    spl6_25 | ~spl6_14 | ~spl6_18),
% 1.34/0.53    inference(avatar_split_clause,[],[f235,f220,f204,f263])).
% 1.34/0.53  fof(f235,plain,(
% 1.34/0.53    r1_tarski(k2_relat_1(sK3),sK0) | (~spl6_14 | ~spl6_18)),
% 1.34/0.53    inference(subsumption_resolution,[],[f233,f205])).
% 1.34/0.53  fof(f233,plain,(
% 1.34/0.53    r1_tarski(k2_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | ~spl6_18),
% 1.34/0.53    inference(resolution,[],[f221,f69])).
% 1.34/0.53  fof(f69,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f38])).
% 1.34/0.53  fof(f38,plain,(
% 1.34/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.34/0.53  fof(f257,plain,(
% 1.34/0.53    spl6_23 | ~spl6_9),
% 1.34/0.53    inference(avatar_split_clause,[],[f132,f117,f255])).
% 1.34/0.53  fof(f132,plain,(
% 1.34/0.53    k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4) | ~spl6_9),
% 1.34/0.53    inference(resolution,[],[f118,f70])).
% 1.34/0.53  fof(f70,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f39])).
% 1.34/0.53  fof(f39,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(ennf_transformation,[],[f8])).
% 1.34/0.53  fof(f8,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.34/0.53  fof(f248,plain,(
% 1.34/0.53    spl6_21 | ~spl6_6 | ~spl6_9),
% 1.34/0.53    inference(avatar_split_clause,[],[f158,f117,f101,f246])).
% 1.34/0.53  fof(f158,plain,(
% 1.34/0.53    sK0 = k1_relat_1(sK4) | (~spl6_6 | ~spl6_9)),
% 1.34/0.53    inference(subsumption_resolution,[],[f156,f157])).
% 1.34/0.53  fof(f157,plain,(
% 1.34/0.53    v1_relat_1(sK4) | ~spl6_9),
% 1.34/0.53    inference(subsumption_resolution,[],[f136,f77])).
% 1.34/0.53  fof(f77,plain,(
% 1.34/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.34/0.53  fof(f136,plain,(
% 1.34/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK4) | ~spl6_9),
% 1.34/0.53    inference(resolution,[],[f118,f78])).
% 1.34/0.53  fof(f78,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f46])).
% 1.34/0.53  fof(f46,plain,(
% 1.34/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.34/0.53    inference(ennf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.34/0.53  fof(f156,plain,(
% 1.34/0.53    sK0 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | (~spl6_6 | ~spl6_9)),
% 1.34/0.53    inference(subsumption_resolution,[],[f107,f134])).
% 1.34/0.53  fof(f134,plain,(
% 1.34/0.53    v4_relat_1(sK4,sK0) | ~spl6_9),
% 1.34/0.53    inference(resolution,[],[f118,f75])).
% 1.34/0.53  fof(f75,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f45])).
% 1.34/0.53  fof(f45,plain,(
% 1.34/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(ennf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.34/0.53  fof(f107,plain,(
% 1.34/0.53    ~v4_relat_1(sK4,sK0) | sK0 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl6_6),
% 1.34/0.53    inference(resolution,[],[f102,f74])).
% 1.34/0.53  fof(f226,plain,(
% 1.34/0.53    spl6_19 | ~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_10),
% 1.34/0.53    inference(avatar_split_clause,[],[f189,f121,f113,f93,f85,f224])).
% 1.34/0.53  fof(f189,plain,(
% 1.34/0.53    v1_partfun1(sK3,sK1) | (~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_10)),
% 1.34/0.53    inference(subsumption_resolution,[],[f188,f114])).
% 1.34/0.53  fof(f188,plain,(
% 1.34/0.53    ~v1_funct_2(sK3,sK1,sK0) | v1_partfun1(sK3,sK1) | (~spl6_2 | spl6_4 | ~spl6_10)),
% 1.34/0.53    inference(subsumption_resolution,[],[f187,f86])).
% 1.34/0.53  fof(f187,plain,(
% 1.34/0.53    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_partfun1(sK3,sK1) | (spl6_4 | ~spl6_10)),
% 1.34/0.53    inference(subsumption_resolution,[],[f166,f94])).
% 1.34/0.53  fof(f166,plain,(
% 1.34/0.53    v1_xboole_0(sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_partfun1(sK3,sK1) | ~spl6_10),
% 1.34/0.53    inference(resolution,[],[f122,f65])).
% 1.34/0.53  fof(f65,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f35])).
% 1.34/0.53  fof(f35,plain,(
% 1.34/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.34/0.53    inference(flattening,[],[f34])).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f12])).
% 1.34/0.53  fof(f12,axiom,(
% 1.34/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.34/0.53  fof(f222,plain,(
% 1.34/0.53    spl6_18 | ~spl6_10),
% 1.34/0.53    inference(avatar_split_clause,[],[f170,f121,f220])).
% 1.34/0.53  fof(f170,plain,(
% 1.34/0.53    v5_relat_1(sK3,sK0) | ~spl6_10),
% 1.34/0.53    inference(resolution,[],[f122,f76])).
% 1.34/0.53  fof(f76,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f45])).
% 1.34/0.53  fof(f218,plain,(
% 1.34/0.53    spl6_17 | ~spl6_10),
% 1.34/0.53    inference(avatar_split_clause,[],[f169,f121,f216])).
% 1.34/0.53  fof(f169,plain,(
% 1.34/0.53    v4_relat_1(sK3,sK1) | ~spl6_10),
% 1.34/0.53    inference(resolution,[],[f122,f75])).
% 1.34/0.53  fof(f206,plain,(
% 1.34/0.53    spl6_14 | ~spl6_10),
% 1.34/0.53    inference(avatar_split_clause,[],[f190,f121,f204])).
% 1.34/0.53  fof(f190,plain,(
% 1.34/0.53    v1_relat_1(sK3) | ~spl6_10),
% 1.34/0.53    inference(subsumption_resolution,[],[f171,f77])).
% 1.34/0.53  fof(f171,plain,(
% 1.34/0.53    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3) | ~spl6_10),
% 1.34/0.53    inference(resolution,[],[f122,f78])).
% 1.34/0.53  fof(f198,plain,(
% 1.34/0.53    ~spl6_12),
% 1.34/0.53    inference(avatar_split_clause,[],[f49,f196])).
% 1.34/0.53  fof(f196,plain,(
% 1.34/0.53    spl6_12 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.34/0.53  fof(f49,plain,(
% 1.34/0.53    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.34/0.53    inference(flattening,[],[f20])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.34/0.53    inference(ennf_transformation,[],[f19])).
% 1.34/0.53  fof(f19,negated_conjecture,(
% 1.34/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 1.34/0.53    inference(negated_conjecture,[],[f18])).
% 1.34/0.53  fof(f18,conjecture,(
% 1.34/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).
% 1.34/0.53  fof(f123,plain,(
% 1.34/0.53    spl6_10),
% 1.34/0.53    inference(avatar_split_clause,[],[f54,f121])).
% 1.34/0.53  fof(f54,plain,(
% 1.34/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f119,plain,(
% 1.34/0.53    spl6_9),
% 1.34/0.53    inference(avatar_split_clause,[],[f51,f117])).
% 1.34/0.53  fof(f51,plain,(
% 1.34/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f115,plain,(
% 1.34/0.53    spl6_8),
% 1.34/0.53    inference(avatar_split_clause,[],[f53,f113])).
% 1.34/0.53  fof(f53,plain,(
% 1.34/0.53    v1_funct_2(sK3,sK1,sK0)),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f111,plain,(
% 1.34/0.53    spl6_7 | spl6_3 | ~spl6_5),
% 1.34/0.53    inference(avatar_split_clause,[],[f106,f97,f89,f109])).
% 1.34/0.53  fof(f106,plain,(
% 1.34/0.53    r2_hidden(sK5,sK1) | (spl6_3 | ~spl6_5)),
% 1.34/0.53    inference(subsumption_resolution,[],[f104,f90])).
% 1.34/0.53  fof(f104,plain,(
% 1.34/0.53    v1_xboole_0(sK1) | r2_hidden(sK5,sK1) | ~spl6_5),
% 1.34/0.53    inference(resolution,[],[f98,f72])).
% 1.34/0.53  fof(f72,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f42])).
% 1.34/0.53  fof(f42,plain,(
% 1.34/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.34/0.53    inference(flattening,[],[f41])).
% 1.34/0.53  fof(f41,plain,(
% 1.34/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.34/0.53  fof(f103,plain,(
% 1.34/0.53    spl6_6),
% 1.34/0.53    inference(avatar_split_clause,[],[f48,f101])).
% 1.34/0.53  fof(f48,plain,(
% 1.34/0.53    v1_partfun1(sK4,sK0)),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f99,plain,(
% 1.34/0.53    spl6_5),
% 1.34/0.53    inference(avatar_split_clause,[],[f47,f97])).
% 1.34/0.53  fof(f47,plain,(
% 1.34/0.53    m1_subset_1(sK5,sK1)),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f95,plain,(
% 1.34/0.53    ~spl6_4),
% 1.34/0.53    inference(avatar_split_clause,[],[f56,f93])).
% 1.34/0.53  fof(f56,plain,(
% 1.34/0.53    ~v1_xboole_0(sK0)),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f91,plain,(
% 1.34/0.53    ~spl6_3),
% 1.34/0.53    inference(avatar_split_clause,[],[f55,f89])).
% 1.34/0.53  fof(f55,plain,(
% 1.34/0.53    ~v1_xboole_0(sK1)),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f87,plain,(
% 1.34/0.53    spl6_2),
% 1.34/0.53    inference(avatar_split_clause,[],[f52,f85])).
% 1.34/0.53  fof(f52,plain,(
% 1.34/0.53    v1_funct_1(sK3)),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f83,plain,(
% 1.34/0.53    spl6_1),
% 1.34/0.53    inference(avatar_split_clause,[],[f50,f81])).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    v1_funct_1(sK4)),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (19929)------------------------------
% 1.34/0.53  % (19929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (19929)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (19929)Memory used [KB]: 6652
% 1.34/0.53  % (19929)Time elapsed: 0.088 s
% 1.34/0.53  % (19929)------------------------------
% 1.34/0.53  % (19929)------------------------------
% 1.34/0.53  % (19928)Success in time 0.169 s
%------------------------------------------------------------------------------
