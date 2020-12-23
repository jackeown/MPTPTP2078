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
% DateTime   : Thu Dec  3 13:08:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 217 expanded)
%              Number of leaves         :   25 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  455 ( 951 expanded)
%              Number of equality atoms :   40 (  76 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f224,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f65,f69,f81,f86,f90,f121,f125,f137,f204,f211,f217,f222,f223])).

fof(f223,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f222,plain,
    ( spl6_31
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f218,f88,f84,f79,f67,f63,f59,f55,f51,f47,f220])).

fof(f220,plain,
    ( spl6_31
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f47,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f51,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f55,plain,
    ( spl6_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f59,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f63,plain,
    ( spl6_5
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f67,plain,
    ( spl6_6
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f79,plain,
    ( spl6_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f84,plain,
    ( spl6_9
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f88,plain,
    ( spl6_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f218,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f200,f64])).

fof(f64,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f199,f68])).

fof(f68,plain,
    ( v1_partfun1(sK4,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ v1_partfun1(sK4,sK0)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f198,f48])).

fof(f48,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X0,sK1)
        | ~ v1_partfun1(sK4,sK0)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) )
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f117,f85])).

fof(f85,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f117,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X3,sK1)
        | ~ v1_partfun1(X1,sK0)
        | k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,sK3,X1),X3) = k1_funct_1(X1,k3_funct_2(sK1,sK0,sK3,X3)) )
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f116,f60])).

fof(f60,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f116,plain,
    ( ! [X2,X3,X1] :
        ( v1_xboole_0(sK0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ m1_subset_1(X3,sK1)
        | ~ v1_partfun1(X1,sK0)
        | k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,sK3,X1),X3) = k1_funct_1(X1,k3_funct_2(sK1,sK0,sK3,X3)) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f115,f80])).

fof(f80,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f115,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ m1_subset_1(X3,sK1)
        | ~ v1_partfun1(X1,sK0)
        | k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,sK3,X1),X3) = k1_funct_1(X1,k3_funct_2(sK1,sK0,sK3,X3)) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f114,f52])).

fof(f52,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f114,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ m1_subset_1(X3,sK1)
        | ~ v1_partfun1(X1,sK0)
        | k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,sK3,X1),X3) = k1_funct_1(X1,k3_funct_2(sK1,sK0,sK3,X3)) )
    | spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f108,f56])).

fof(f56,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f108,plain,
    ( ! [X2,X3,X1] :
        ( v1_xboole_0(sK1)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ m1_subset_1(X3,sK1)
        | ~ v1_partfun1(X1,sK0)
        | k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,sK3,X1),X3) = k1_funct_1(X1,k3_funct_2(sK1,sK0,sK3,X3)) )
    | ~ spl6_10 ),
    inference(resolution,[],[f89,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X5,X1)
      | ~ v1_partfun1(X4,X0)
      | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

fof(f89,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f217,plain,
    ( spl6_30
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f212,f209,f135,f119,f84,f67,f47,f215])).

fof(f215,plain,
    ( spl6_30
  <=> k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f119,plain,
    ( spl6_11
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

% (9701)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f135,plain,
    ( spl6_15
  <=> v5_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f209,plain,
    ( spl6_29
  <=> r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f212,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_29 ),
    inference(resolution,[],[f210,f149])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k7_partfun1(sK2,sK4,X0) = k1_funct_1(sK4,X0) )
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f148,f99])).

fof(f99,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f98,f93])).

fof(f93,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_9 ),
    inference(resolution,[],[f85,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f98,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f73,f91])).

fof(f91,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f85,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f73,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | sK0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_6 ),
    inference(resolution,[],[f68,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f148,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK4))
        | k7_partfun1(sK2,sK4,X0) = k1_funct_1(sK4,X0) )
    | ~ spl6_1
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f147,f48])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ r2_hidden(X0,k1_relat_1(sK4))
        | k7_partfun1(sK2,sK4,X0) = k1_funct_1(sK4,X0) )
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f146,f120])).

fof(f120,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK4)
        | ~ v1_funct_1(sK4)
        | ~ r2_hidden(X0,k1_relat_1(sK4))
        | k7_partfun1(sK2,sK4,X0) = k1_funct_1(sK4,X0) )
    | ~ spl6_15 ),
    inference(resolution,[],[f136,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f136,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f210,plain,
    ( r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),sK0)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f209])).

fof(f211,plain,
    ( spl6_29
    | spl6_4
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f207,f202,f59,f209])).

fof(f202,plain,
    ( spl6_28
  <=> m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f207,plain,
    ( r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),sK0)
    | spl6_4
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f206,f60])).

fof(f206,plain,
    ( r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_28 ),
    inference(resolution,[],[f203,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f203,plain,
    ( m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,
    ( spl6_28
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f185,f88,f79,f63,f55,f51,f202])).

fof(f185,plain,
    ( m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(resolution,[],[f113,f64])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f112,f56])).

fof(f112,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f111,f80])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) )
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f107,f52])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f89,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f137,plain,
    ( spl6_15
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f92,f84,f135])).

fof(f92,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ spl6_9 ),
    inference(resolution,[],[f85,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f125,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f25,f123])).

fof(f123,plain,
    ( spl6_12
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f25,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f121,plain,
    ( spl6_11
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f93,f84,f119])).

fof(f90,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f30,f88])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f86,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f27,f84])).

fof(f27,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f81,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f29,f79])).

fof(f29,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f69,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f24,f67])).

fof(f24,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f23,f63])).

fof(f23,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f31,f55])).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f28,f51])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f11])).

% (9708)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (9702)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (9708)Refutation not found, incomplete strategy% (9708)------------------------------
% (9708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9708)Termination reason: Refutation not found, incomplete strategy

% (9708)Memory used [KB]: 10618
% (9708)Time elapsed: 0.071 s
% (9708)------------------------------
% (9708)------------------------------
% (9689)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f49,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:46:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.45  % (9686)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.45  % (9691)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.46  % (9690)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.46  % (9686)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (9707)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f224,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f65,f69,f81,f86,f90,f121,f125,f137,f204,f211,f217,f222,f223])).
% 0.20/0.46  fof(f223,plain,(
% 0.20/0.46    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.46  fof(f222,plain,(
% 0.20/0.46    spl6_31 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_9 | ~spl6_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f218,f88,f84,f79,f67,f63,f59,f55,f51,f47,f220])).
% 0.20/0.46  fof(f220,plain,(
% 0.20/0.46    spl6_31 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    spl6_1 <=> v1_funct_1(sK4)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    spl6_2 <=> v1_funct_1(sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    spl6_3 <=> v1_xboole_0(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    spl6_4 <=> v1_xboole_0(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    spl6_5 <=> m1_subset_1(sK5,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    spl6_6 <=> v1_partfun1(sK4,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    spl6_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    spl6_9 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    spl6_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.46  fof(f218,plain,(
% 0.20/0.46    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 0.20/0.46    inference(resolution,[],[f200,f64])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    m1_subset_1(sK5,sK1) | ~spl6_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f63])).
% 0.20/0.46  fof(f200,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_6 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f199,f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    v1_partfun1(sK4,sK0) | ~spl6_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f67])).
% 0.20/0.46  fof(f199,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~v1_partfun1(sK4,sK0) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f198,f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    v1_funct_1(sK4) | ~spl6_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f47])).
% 0.20/0.46  fof(f198,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_funct_1(sK4) | ~m1_subset_1(X0,sK1) | ~v1_partfun1(sK4,sK0) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))) ) | (~spl6_2 | spl6_3 | spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 0.20/0.46    inference(resolution,[],[f117,f85])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f84])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~v1_funct_1(X1) | ~m1_subset_1(X3,sK1) | ~v1_partfun1(X1,sK0) | k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,sK3,X1),X3) = k1_funct_1(X1,k3_funct_2(sK1,sK0,sK3,X3))) ) | (~spl6_2 | spl6_3 | spl6_4 | ~spl6_8 | ~spl6_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f116,f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ~v1_xboole_0(sK0) | spl6_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f59])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    ( ! [X2,X3,X1] : (v1_xboole_0(sK0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~m1_subset_1(X3,sK1) | ~v1_partfun1(X1,sK0) | k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,sK3,X1),X3) = k1_funct_1(X1,k3_funct_2(sK1,sK0,sK3,X3))) ) | (~spl6_2 | spl6_3 | ~spl6_8 | ~spl6_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f115,f80])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    v1_funct_2(sK3,sK1,sK0) | ~spl6_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f79])).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    ( ! [X2,X3,X1] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~m1_subset_1(X3,sK1) | ~v1_partfun1(X1,sK0) | k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,sK3,X1),X3) = k1_funct_1(X1,k3_funct_2(sK1,sK0,sK3,X3))) ) | (~spl6_2 | spl6_3 | ~spl6_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f114,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    v1_funct_1(sK3) | ~spl6_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f51])).
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    ( ! [X2,X3,X1] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~m1_subset_1(X3,sK1) | ~v1_partfun1(X1,sK0) | k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,sK3,X1),X3) = k1_funct_1(X1,k3_funct_2(sK1,sK0,sK3,X3))) ) | (spl6_3 | ~spl6_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f108,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ~v1_xboole_0(sK1) | spl6_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f55])).
% 0.20/0.46  fof(f108,plain,(
% 0.20/0.46    ( ! [X2,X3,X1] : (v1_xboole_0(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~m1_subset_1(X3,sK1) | ~v1_partfun1(X1,sK0) | k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,sK3,X1),X3) = k1_funct_1(X1,k3_funct_2(sK1,sK0,sK3,X3))) ) | ~spl6_10),
% 0.20/0.46    inference(resolution,[],[f89,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | v1_xboole_0(X0) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X5,X1) | ~v1_partfun1(X4,X0) | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.46    inference(flattening,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f88])).
% 0.20/0.46  fof(f217,plain,(
% 0.20/0.46    spl6_30 | ~spl6_1 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_15 | ~spl6_29),
% 0.20/0.46    inference(avatar_split_clause,[],[f212,f209,f135,f119,f84,f67,f47,f215])).
% 0.20/0.46  fof(f215,plain,(
% 0.20/0.46    spl6_30 <=> k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.20/0.46  fof(f119,plain,(
% 0.20/0.46    spl6_11 <=> v1_relat_1(sK4)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.46  % (9701)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  fof(f135,plain,(
% 0.20/0.46    spl6_15 <=> v5_relat_1(sK4,sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.46  fof(f209,plain,(
% 0.20/0.46    spl6_29 <=> r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.46  fof(f212,plain,(
% 0.20/0.46    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | (~spl6_1 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_15 | ~spl6_29)),
% 0.20/0.46    inference(resolution,[],[f210,f149])).
% 0.20/0.46  fof(f149,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,sK0) | k7_partfun1(sK2,sK4,X0) = k1_funct_1(sK4,X0)) ) | (~spl6_1 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_15)),
% 0.20/0.46    inference(forward_demodulation,[],[f148,f99])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    sK0 = k1_relat_1(sK4) | (~spl6_6 | ~spl6_9)),
% 0.20/0.46    inference(subsumption_resolution,[],[f98,f93])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    v1_relat_1(sK4) | ~spl6_9),
% 0.20/0.46    inference(resolution,[],[f85,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    sK0 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | (~spl6_6 | ~spl6_9)),
% 0.20/0.46    inference(subsumption_resolution,[],[f73,f91])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    v4_relat_1(sK4,sK0) | ~spl6_9),
% 0.20/0.46    inference(resolution,[],[f85,f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    ~v4_relat_1(sK4,sK0) | sK0 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl6_6),
% 0.20/0.46    inference(resolution,[],[f68,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.46  fof(f148,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK4)) | k7_partfun1(sK2,sK4,X0) = k1_funct_1(sK4,X0)) ) | (~spl6_1 | ~spl6_11 | ~spl6_15)),
% 0.20/0.46    inference(subsumption_resolution,[],[f147,f48])).
% 0.20/0.46  fof(f147,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_funct_1(sK4) | ~r2_hidden(X0,k1_relat_1(sK4)) | k7_partfun1(sK2,sK4,X0) = k1_funct_1(sK4,X0)) ) | (~spl6_11 | ~spl6_15)),
% 0.20/0.46    inference(subsumption_resolution,[],[f146,f120])).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    v1_relat_1(sK4) | ~spl6_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f119])).
% 0.20/0.46  fof(f146,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~r2_hidden(X0,k1_relat_1(sK4)) | k7_partfun1(sK2,sK4,X0) = k1_funct_1(sK4,X0)) ) | ~spl6_15),
% 0.20/0.46    inference(resolution,[],[f136,f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.46  fof(f136,plain,(
% 0.20/0.46    v5_relat_1(sK4,sK2) | ~spl6_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f135])).
% 0.20/0.46  fof(f210,plain,(
% 0.20/0.46    r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),sK0) | ~spl6_29),
% 0.20/0.46    inference(avatar_component_clause,[],[f209])).
% 0.20/0.46  fof(f211,plain,(
% 0.20/0.46    spl6_29 | spl6_4 | ~spl6_28),
% 0.20/0.46    inference(avatar_split_clause,[],[f207,f202,f59,f209])).
% 0.20/0.46  fof(f202,plain,(
% 0.20/0.46    spl6_28 <=> m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.46  fof(f207,plain,(
% 0.20/0.46    r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),sK0) | (spl6_4 | ~spl6_28)),
% 0.20/0.46    inference(subsumption_resolution,[],[f206,f60])).
% 0.20/0.46  fof(f206,plain,(
% 0.20/0.46    r2_hidden(k3_funct_2(sK1,sK0,sK3,sK5),sK0) | v1_xboole_0(sK0) | ~spl6_28),
% 0.20/0.46    inference(resolution,[],[f203,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.46  fof(f203,plain,(
% 0.20/0.46    m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0) | ~spl6_28),
% 0.20/0.46    inference(avatar_component_clause,[],[f202])).
% 0.20/0.46  fof(f204,plain,(
% 0.20/0.46    spl6_28 | ~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f185,f88,f79,f63,f55,f51,f202])).
% 0.20/0.46  fof(f185,plain,(
% 0.20/0.46    m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0) | (~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10)),
% 0.20/0.46    inference(resolution,[],[f113,f64])).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)) ) | (~spl6_2 | spl6_3 | ~spl6_8 | ~spl6_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f112,f56])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)) ) | (~spl6_2 | ~spl6_8 | ~spl6_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f111,f80])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)) ) | (~spl6_2 | ~spl6_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f107,f52])).
% 0.20/0.46  fof(f107,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)) ) | ~spl6_10),
% 0.20/0.46    inference(resolution,[],[f89,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.46    inference(flattening,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    spl6_15 | ~spl6_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f92,f84,f135])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    v5_relat_1(sK4,sK2) | ~spl6_9),
% 0.20/0.46    inference(resolution,[],[f85,f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f125,plain,(
% 0.20/0.46    ~spl6_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f25,f123])).
% 0.20/0.46  fof(f123,plain,(
% 0.20/0.46    spl6_12 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.46    inference(flattening,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.46    inference(negated_conjecture,[],[f8])).
% 0.20/0.46  fof(f8,conjecture,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    spl6_11 | ~spl6_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f93,f84,f119])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    spl6_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f30,f88])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    spl6_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f84])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    spl6_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f29,f79])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    spl6_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f24,f67])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    v1_partfun1(sK4,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    spl6_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f63])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    m1_subset_1(sK5,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    ~spl6_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f32,f59])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ~v1_xboole_0(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ~spl6_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f31,f55])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ~v1_xboole_0(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    spl6_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f28,f51])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    v1_funct_1(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  % (9708)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (9702)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (9708)Refutation not found, incomplete strategy% (9708)------------------------------
% 0.20/0.47  % (9708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (9708)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (9708)Memory used [KB]: 10618
% 0.20/0.47  % (9708)Time elapsed: 0.071 s
% 0.20/0.47  % (9708)------------------------------
% 0.20/0.47  % (9708)------------------------------
% 0.20/0.47  % (9689)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    spl6_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f26,f47])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    v1_funct_1(sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (9686)------------------------------
% 0.20/0.48  % (9686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9686)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (9686)Memory used [KB]: 6268
% 0.20/0.48  % (9686)Time elapsed: 0.070 s
% 0.20/0.48  % (9686)------------------------------
% 0.20/0.48  % (9686)------------------------------
% 0.20/0.48  % (9683)Success in time 0.133 s
%------------------------------------------------------------------------------
