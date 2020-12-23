%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 434 expanded)
%              Number of leaves         :   32 ( 145 expanded)
%              Depth                    :   16
%              Number of atoms          :  466 (1342 expanded)
%              Number of equality atoms :   79 ( 183 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f79,f83,f90,f94,f115,f122,f127,f131,f143,f162,f211,f225,f292,f358,f359,f393,f396,f397])).

fof(f397,plain,
    ( sK3 != k7_relat_1(sK3,sK0)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != sK0
    | k1_xboole_0 != sK1
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f396,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | spl4_9
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6
    | spl4_9
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f394,f357])).

fof(f357,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl4_25
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f394,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_9 ),
    inference(forward_demodulation,[],[f121,f107])).

fof(f107,plain,
    ( ! [X2] : k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f97,f74])).

fof(f74,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f97,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK3)
        | k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_6 ),
    inference(resolution,[],[f93,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f93,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f121,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_9
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f393,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | spl4_10
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6
    | spl4_10
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f385,f126])).

fof(f126,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_10
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f385,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_24 ),
    inference(superposition,[],[f284,f291])).

fof(f291,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl4_24
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f284,plain,
    ( ! [X2] : m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f283,f259])).

fof(f259,plain,
    ( ! [X11] : v1_relat_1(k7_relat_1(sK3,X11))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f258,f107])).

fof(f258,plain,
    ( ! [X11] : v1_relat_1(k2_partfun1(sK0,sK1,sK3,X11))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f241,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f241,plain,
    ( ! [X11] :
        ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
        | v1_relat_1(k2_partfun1(sK0,sK1,sK3,X11)) )
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(resolution,[],[f106,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f106,plain,
    ( ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f96,f74])).

fof(f96,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl4_6 ),
    inference(resolution,[],[f93,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f283,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X2))
        | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1))) )
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f279,f231])).

fof(f231,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK3,X0))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(superposition,[],[f104,f107])).

fof(f104,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f95,f74])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f93,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f279,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(k7_relat_1(sK3,X2))
        | ~ v1_relat_1(k7_relat_1(sK3,X2))
        | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1))) )
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(resolution,[],[f266,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f266,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f264,f259])).

fof(f264,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
        | ~ v1_relat_1(k7_relat_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(resolution,[],[f257,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f257,plain,
    ( ! [X10] : v5_relat_1(k7_relat_1(sK3,X10),sK1)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f240,f107])).

fof(f240,plain,
    ( ! [X10] : v5_relat_1(k2_partfun1(sK0,sK1,sK3,X10),sK1)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(resolution,[],[f106,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f359,plain,
    ( sK3 != k7_relat_1(sK3,sK0)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f358,plain,
    ( spl4_25
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f351,f290,f92,f73,f356])).

fof(f351,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_24 ),
    inference(superposition,[],[f282,f291])).

fof(f282,plain,
    ( ! [X1] : v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f281,f259])).

fof(f281,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X1))
        | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) )
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f278,f231])).

fof(f278,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k7_relat_1(sK3,X1))
        | ~ v1_relat_1(k7_relat_1(sK3,X1))
        | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) )
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(resolution,[],[f266,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f292,plain,
    ( spl4_24
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f286,f141,f113,f77,f290])).

fof(f77,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f113,plain,
    ( spl4_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f141,plain,
    ( spl4_13
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f286,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(resolution,[],[f164,f78])).

fof(f78,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f163,f114])).

fof(f114,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(sK3)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_13 ),
    inference(superposition,[],[f54,f142])).

fof(f142,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f225,plain,
    ( spl4_22
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f137,f129,f113,f223])).

fof(f223,plain,
    ( spl4_22
  <=> sK3 = k7_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f129,plain,
    ( spl4_11
  <=> v4_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f137,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f136,f114])).

fof(f136,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK0)
    | ~ spl4_11 ),
    inference(resolution,[],[f130,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f130,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f211,plain,
    ( spl4_21
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f193,f160,f209])).

fof(f209,plain,
    ( spl4_21
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f160,plain,
    ( spl4_14
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f193,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_14 ),
    inference(resolution,[],[f161,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f161,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f149,f85,f77,f160])).

fof(f85,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f149,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f78,f86])).

fof(f86,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f143,plain,
    ( spl4_13
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f110,f92,f88,f81,f141])).

fof(f81,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f88,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f110,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f100,f109])).

fof(f109,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f108,f82])).

fof(f82,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f108,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f99,f89])).

fof(f89,plain,
    ( k1_xboole_0 != sK1
    | spl4_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f93,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f100,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f93,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f131,plain,
    ( spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f101,f92,f129])).

fof(f101,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f93,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f127,plain,
    ( ~ spl4_10
    | ~ spl4_1
    | ~ spl4_6
    | spl4_8 ),
    inference(avatar_split_clause,[],[f123,f117,f92,f73,f125])).

fof(f117,plain,
    ( spl4_8
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f123,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_6
    | spl4_8 ),
    inference(forward_demodulation,[],[f118,f107])).

fof(f118,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f122,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f105,f92,f73,f120,f117])).

fof(f105,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f35,f104])).

fof(f35,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f115,plain,
    ( spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f111,f92,f113])).

fof(f111,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f103,f56])).

fof(f103,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f93,f55])).

fof(f94,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f39,f92])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f36,f88,f85])).

fof(f36,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f38,f81])).

fof(f38,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f75,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f37,f73])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (22427)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (22419)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (22420)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (22427)Refutation not found, incomplete strategy% (22427)------------------------------
% 0.20/0.47  % (22427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22427)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (22427)Memory used [KB]: 10618
% 0.20/0.47  % (22427)Time elapsed: 0.065 s
% 0.20/0.47  % (22427)------------------------------
% 0.20/0.47  % (22427)------------------------------
% 0.20/0.47  % (22412)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (22413)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (22415)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (22411)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (22421)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (22423)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (22408)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (22408)Refutation not found, incomplete strategy% (22408)------------------------------
% 0.20/0.49  % (22408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22408)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (22408)Memory used [KB]: 10618
% 0.20/0.49  % (22408)Time elapsed: 0.092 s
% 0.20/0.49  % (22408)------------------------------
% 0.20/0.49  % (22408)------------------------------
% 0.20/0.49  % (22407)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (22424)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (22418)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (22410)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (22426)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (22409)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (22414)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (22425)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (22416)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (22422)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (22417)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (22407)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f398,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f75,f79,f83,f90,f94,f115,f122,f127,f131,f143,f162,f211,f225,f292,f358,f359,f393,f396,f397])).
% 0.20/0.52  fof(f397,plain,(
% 0.20/0.52    sK3 != k7_relat_1(sK3,sK0) | k1_xboole_0 != sK2 | k1_xboole_0 != sK0 | k1_xboole_0 != sK1 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f396,plain,(
% 0.20/0.52    ~spl4_1 | ~spl4_6 | spl4_9 | ~spl4_25),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f395])).
% 0.20/0.52  fof(f395,plain,(
% 0.20/0.52    $false | (~spl4_1 | ~spl4_6 | spl4_9 | ~spl4_25)),
% 0.20/0.52    inference(subsumption_resolution,[],[f394,f357])).
% 0.20/0.52  fof(f357,plain,(
% 0.20/0.52    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_25),
% 0.20/0.52    inference(avatar_component_clause,[],[f356])).
% 0.20/0.52  fof(f356,plain,(
% 0.20/0.52    spl4_25 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.52  fof(f394,plain,(
% 0.20/0.52    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_1 | ~spl4_6 | spl4_9)),
% 0.20/0.52    inference(forward_demodulation,[],[f121,f107])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    ( ! [X2] : (k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f97,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    v1_funct_1(sK3) | ~spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    spl4_1 <=> v1_funct_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X2] : (~v1_funct_1(sK3) | k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_6),
% 0.20/0.52    inference(resolution,[],[f93,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f92])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    spl4_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f120])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    spl4_9 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.52  fof(f393,plain,(
% 0.20/0.52    ~spl4_1 | ~spl4_6 | spl4_10 | ~spl4_24),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f392])).
% 0.20/0.52  fof(f392,plain,(
% 0.20/0.52    $false | (~spl4_1 | ~spl4_6 | spl4_10 | ~spl4_24)),
% 0.20/0.52    inference(subsumption_resolution,[],[f385,f126])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f125])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    spl4_10 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.52  fof(f385,plain,(
% 0.20/0.52    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_6 | ~spl4_24)),
% 0.20/0.52    inference(superposition,[],[f284,f291])).
% 0.20/0.52  fof(f291,plain,(
% 0.20/0.52    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_24),
% 0.20/0.52    inference(avatar_component_clause,[],[f290])).
% 0.20/0.52  fof(f290,plain,(
% 0.20/0.52    spl4_24 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.52  fof(f284,plain,(
% 0.20/0.52    ( ! [X2] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f283,f259])).
% 0.20/0.52  fof(f259,plain,(
% 0.20/0.52    ( ! [X11] : (v1_relat_1(k7_relat_1(sK3,X11))) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(forward_demodulation,[],[f258,f107])).
% 0.20/0.52  fof(f258,plain,(
% 0.20/0.52    ( ! [X11] : (v1_relat_1(k2_partfun1(sK0,sK1,sK3,X11))) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f241,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.52  fof(f241,plain,(
% 0.20/0.52    ( ! [X11] : (~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(k2_partfun1(sK0,sK1,sK3,X11))) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(resolution,[],[f106,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f96,f74])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ( ! [X1] : (~v1_funct_1(sK3) | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_6),
% 0.20/0.52    inference(resolution,[],[f93,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.20/0.52  fof(f283,plain,(
% 0.20/0.52    ( ! [X2] : (~v1_relat_1(k7_relat_1(sK3,X2)) | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f279,f231])).
% 0.20/0.52  fof(f231,plain,(
% 0.20/0.52    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(superposition,[],[f104,f107])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f95,f74])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_1(sK3) | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) ) | ~spl4_6),
% 0.20/0.52    inference(resolution,[],[f93,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f279,plain,(
% 0.20/0.52    ( ! [X2] : (~v1_funct_1(k7_relat_1(sK3,X2)) | ~v1_relat_1(k7_relat_1(sK3,X2)) | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(resolution,[],[f266,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.52  fof(f266,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f264,f259])).
% 0.20/0.52  fof(f264,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(resolution,[],[f257,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.52  fof(f257,plain,(
% 0.20/0.52    ( ! [X10] : (v5_relat_1(k7_relat_1(sK3,X10),sK1)) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(forward_demodulation,[],[f240,f107])).
% 0.20/0.52  fof(f240,plain,(
% 0.20/0.52    ( ! [X10] : (v5_relat_1(k2_partfun1(sK0,sK1,sK3,X10),sK1)) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(resolution,[],[f106,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.52  fof(f359,plain,(
% 0.20/0.52    sK3 != k7_relat_1(sK3,sK0) | k1_xboole_0 != sK2 | k1_xboole_0 != sK0 | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f358,plain,(
% 0.20/0.52    spl4_25 | ~spl4_1 | ~spl4_6 | ~spl4_24),
% 0.20/0.52    inference(avatar_split_clause,[],[f351,f290,f92,f73,f356])).
% 0.20/0.52  fof(f351,plain,(
% 0.20/0.52    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_1 | ~spl4_6 | ~spl4_24)),
% 0.20/0.52    inference(superposition,[],[f282,f291])).
% 0.20/0.52  fof(f282,plain,(
% 0.20/0.52    ( ! [X1] : (v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f281,f259])).
% 0.20/0.52  fof(f281,plain,(
% 0.20/0.52    ( ! [X1] : (~v1_relat_1(k7_relat_1(sK3,X1)) | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f278,f231])).
% 0.20/0.52  fof(f278,plain,(
% 0.20/0.52    ( ! [X1] : (~v1_funct_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(k7_relat_1(sK3,X1)) | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(resolution,[],[f266,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f292,plain,(
% 0.20/0.52    spl4_24 | ~spl4_2 | ~spl4_7 | ~spl4_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f286,f141,f113,f77,f290])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    spl4_2 <=> r1_tarski(sK2,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    spl4_7 <=> v1_relat_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    spl4_13 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.52  fof(f286,plain,(
% 0.20/0.52    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_2 | ~spl4_7 | ~spl4_13)),
% 0.20/0.52    inference(resolution,[],[f164,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    r1_tarski(sK2,sK0) | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f77])).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | (~spl4_7 | ~spl4_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f163,f114])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    v1_relat_1(sK3) | ~spl4_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f113])).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_relat_1(sK3) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_13),
% 0.20/0.52    inference(superposition,[],[f54,f142])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    sK0 = k1_relat_1(sK3) | ~spl4_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f141])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    spl4_22 | ~spl4_7 | ~spl4_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f137,f129,f113,f223])).
% 0.20/0.52  fof(f223,plain,(
% 0.20/0.52    spl4_22 <=> sK3 = k7_relat_1(sK3,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    spl4_11 <=> v4_relat_1(sK3,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    sK3 = k7_relat_1(sK3,sK0) | (~spl4_7 | ~spl4_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f136,f114])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK0) | ~spl4_11),
% 0.20/0.52    inference(resolution,[],[f130,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    v4_relat_1(sK3,sK0) | ~spl4_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f129])).
% 0.20/0.52  fof(f211,plain,(
% 0.20/0.52    spl4_21 | ~spl4_14),
% 0.20/0.52    inference(avatar_split_clause,[],[f193,f160,f209])).
% 0.20/0.52  fof(f209,plain,(
% 0.20/0.52    spl4_21 <=> k1_xboole_0 = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    spl4_14 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    k1_xboole_0 = sK2 | ~spl4_14),
% 0.20/0.52    inference(resolution,[],[f161,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    r1_tarski(sK2,k1_xboole_0) | ~spl4_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f160])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    spl4_14 | ~spl4_2 | ~spl4_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f149,f85,f77,f160])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    spl4_4 <=> k1_xboole_0 = sK0),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    r1_tarski(sK2,k1_xboole_0) | (~spl4_2 | ~spl4_4)),
% 0.20/0.52    inference(superposition,[],[f78,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    k1_xboole_0 = sK0 | ~spl4_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f85])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    spl4_13 | ~spl4_3 | spl4_5 | ~spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f110,f92,f88,f81,f141])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    spl4_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl4_5 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    sK0 = k1_relat_1(sK3) | (~spl4_3 | spl4_5 | ~spl4_6)),
% 0.20/0.52    inference(forward_demodulation,[],[f100,f109])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_3 | spl4_5 | ~spl4_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f108,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    v1_funct_2(sK3,sK0,sK1) | ~spl4_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f81])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl4_5 | ~spl4_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f99,f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | spl4_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f88])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl4_6),
% 0.20/0.52    inference(resolution,[],[f93,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl4_6),
% 0.20/0.52    inference(resolution,[],[f93,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    spl4_11 | ~spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f101,f92,f129])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    v4_relat_1(sK3,sK0) | ~spl4_6),
% 0.20/0.52    inference(resolution,[],[f93,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ~spl4_10 | ~spl4_1 | ~spl4_6 | spl4_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f123,f117,f92,f73,f125])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    spl4_8 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_6 | spl4_8)),
% 0.20/0.52    inference(forward_demodulation,[],[f118,f107])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f117])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    ~spl4_8 | ~spl4_9 | ~spl4_1 | ~spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f105,f92,f73,f120,f117])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f35,f104])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.52    inference(negated_conjecture,[],[f14])).
% 0.20/0.52  fof(f14,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    spl4_7 | ~spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f111,f92,f113])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    v1_relat_1(sK3) | ~spl4_6),
% 0.20/0.52    inference(subsumption_resolution,[],[f103,f56])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl4_6),
% 0.20/0.52    inference(resolution,[],[f93,f55])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f39,f92])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    spl4_4 | ~spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f36,f88,f85])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f38,f81])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f40,f77])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    r1_tarski(sK2,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f37,f73])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    v1_funct_1(sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (22407)------------------------------
% 0.20/0.52  % (22407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22407)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (22407)Memory used [KB]: 6396
% 0.20/0.52  % (22407)Time elapsed: 0.079 s
% 0.20/0.52  % (22407)------------------------------
% 0.20/0.52  % (22407)------------------------------
% 0.20/0.52  % (22406)Success in time 0.167 s
%------------------------------------------------------------------------------
