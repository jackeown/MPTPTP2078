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
% DateTime   : Thu Dec  3 13:03:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 374 expanded)
%              Number of leaves         :   33 ( 129 expanded)
%              Depth                    :   16
%              Number of atoms          :  495 (1178 expanded)
%              Number of equality atoms :   79 ( 171 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f507,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f80,f84,f91,f95,f115,f122,f128,f132,f144,f163,f209,f271,f478,f479,f480,f486,f490,f498,f506])).

fof(f506,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f505])).

fof(f505,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f504,f491])).

fof(f491,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(superposition,[],[f307,f489])).

fof(f489,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f488])).

fof(f488,plain,
    ( spl4_30
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f307,plain,
    ( ! [X2] : m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f306,f124])).

fof(f124,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK3,X0))
    | ~ spl4_7 ),
    inference(resolution,[],[f114,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f114,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f306,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X2))
        | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1))) )
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f302,f228])).

fof(f228,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK3,X0))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(superposition,[],[f105,f108])).

fof(f108,plain,
    ( ! [X2] : k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f98,f75])).

fof(f75,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f98,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK3)
        | k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_6 ),
    inference(resolution,[],[f94,f44])).

fof(f44,plain,(
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

fof(f94,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f105,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f96,f75])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f94,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
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

fof(f302,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(k7_relat_1(sK3,X2))
        | ~ v1_relat_1(k7_relat_1(sK3,X2))
        | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1))) )
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(resolution,[],[f275,f58])).

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

fof(f275,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f274,f124])).

fof(f274,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
        | ~ v1_relat_1(k7_relat_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(resolution,[],[f254,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f254,plain,
    ( ! [X11] : v5_relat_1(k7_relat_1(sK3,X11),sK1)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f237,f108])).

fof(f237,plain,
    ( ! [X11] : v5_relat_1(k2_partfun1(sK0,sK1,sK3,X11),sK1)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(resolution,[],[f107,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f107,plain,
    ( ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f97,f75])).

fof(f97,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl4_6 ),
    inference(resolution,[],[f94,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f504,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_6
    | spl4_8 ),
    inference(forward_demodulation,[],[f118,f108])).

fof(f118,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_8
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f498,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | spl4_29
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | spl4_29
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f493,f485])).

fof(f485,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl4_29
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f493,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(superposition,[],[f305,f489])).

fof(f305,plain,
    ( ! [X1] : v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f304,f124])).

fof(f304,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X1))
        | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) )
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f301,f228])).

fof(f301,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k7_relat_1(sK3,X1))
        | ~ v1_relat_1(k7_relat_1(sK3,X1))
        | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) )
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(resolution,[],[f275,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f490,plain,
    ( spl4_30
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f297,f142,f113,f78,f488])).

fof(f78,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f142,plain,
    ( spl4_13
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f297,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(resolution,[],[f165,f79])).

fof(f79,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f164,f114])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(sK3)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_13 ),
    inference(superposition,[],[f55,f143])).

fof(f143,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f486,plain,
    ( ~ spl4_29
    | ~ spl4_1
    | ~ spl4_6
    | spl4_9 ),
    inference(avatar_split_clause,[],[f481,f120,f93,f74,f484])).

fof(f120,plain,
    ( spl4_9
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f481,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_9 ),
    inference(forward_demodulation,[],[f121,f108])).

fof(f121,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f480,plain,
    ( sK3 != k7_relat_1(sK3,sK0)
    | k1_xboole_0 != sK0
    | k1_xboole_0 != sK1
    | v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f479,plain,
    ( sK3 != k7_relat_1(sK3,sK0)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f478,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | spl4_9
    | ~ spl4_20
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6
    | spl4_9
    | ~ spl4_20
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f476,f390])).

fof(f390,plain,
    ( v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl4_28
  <=> v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f476,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)
    | ~ spl4_1
    | ~ spl4_6
    | spl4_9
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f475,f108])).

fof(f475,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_9
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f121,f208])).

fof(f208,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f271,plain,
    ( spl4_25
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f138,f130,f113,f269])).

fof(f269,plain,
    ( spl4_25
  <=> sK3 = k7_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f130,plain,
    ( spl4_11
  <=> v4_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f138,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f137,f114])).

fof(f137,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK0)
    | ~ spl4_11 ),
    inference(resolution,[],[f131,f59])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f131,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f209,plain,
    ( spl4_20
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f191,f161,f207])).

fof(f161,plain,
    ( spl4_14
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

% (9151)Refutation not found, incomplete strategy% (9151)------------------------------
% (9151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9151)Termination reason: Refutation not found, incomplete strategy

% (9151)Memory used [KB]: 10618
% (9151)Time elapsed: 0.072 s
% (9151)------------------------------
% (9151)------------------------------
% (9154)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (9158)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (9152)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (9153)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (9163)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (9159)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f191,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_14 ),
    inference(resolution,[],[f162,f48])).

fof(f48,plain,(
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

fof(f162,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f150,f86,f78,f161])).

fof(f86,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f150,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f79,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f144,plain,
    ( spl4_13
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f111,f93,f89,f82,f142])).

fof(f82,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f89,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f111,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f102,f110])).

fof(f110,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f109,f83])).

fof(f83,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f109,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f100,f90])).

fof(f90,plain,
    ( k1_xboole_0 != sK1
    | spl4_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f94,f54])).

fof(f54,plain,(
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

fof(f102,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f94,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f132,plain,
    ( spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f103,f93,f130])).

fof(f103,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f128,plain,
    ( ~ spl4_10
    | ~ spl4_1
    | ~ spl4_6
    | spl4_8 ),
    inference(avatar_split_clause,[],[f123,f117,f93,f74,f126])).

fof(f126,plain,
    ( spl4_10
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f123,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_6
    | spl4_8 ),
    inference(forward_demodulation,[],[f118,f108])).

fof(f122,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f106,f93,f74,f120,f117])).

fof(f106,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f36,f105])).

fof(f36,plain,
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
    inference(avatar_split_clause,[],[f101,f93,f113])).

fof(f101,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f94,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f95,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f40,f93])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f37,f89,f86])).

fof(f37,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f39,f82])).

fof(f39,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f78])).

fof(f41,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f38,f74])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (9167)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (9160)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.46  % (9150)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (9150)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (9151)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (9157)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (9166)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f507,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f76,f80,f84,f91,f95,f115,f122,f128,f132,f144,f163,f209,f271,f478,f479,f480,f486,f490,f498,f506])).
% 0.21/0.48  fof(f506,plain,(
% 0.21/0.48    ~spl4_1 | ~spl4_6 | ~spl4_7 | spl4_8 | ~spl4_30),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f505])).
% 0.21/0.48  fof(f505,plain,(
% 0.21/0.48    $false | (~spl4_1 | ~spl4_6 | ~spl4_7 | spl4_8 | ~spl4_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f504,f491])).
% 0.21/0.48  fof(f491,plain,(
% 0.21/0.48    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_6 | ~spl4_7 | ~spl4_30)),
% 0.21/0.48    inference(superposition,[],[f307,f489])).
% 0.21/0.48  fof(f489,plain,(
% 0.21/0.48    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f488])).
% 0.21/0.48  fof(f488,plain,(
% 0.21/0.48    spl4_30 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.48  fof(f307,plain,(
% 0.21/0.48    ( ! [X2] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) ) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f306,f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) ) | ~spl4_7),
% 0.21/0.48    inference(resolution,[],[f114,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f113])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl4_7 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f306,plain,(
% 0.21/0.48    ( ! [X2] : (~v1_relat_1(k7_relat_1(sK3,X2)) | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) ) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f302,f228])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) ) | (~spl4_1 | ~spl4_6)),
% 0.21/0.48    inference(superposition,[],[f105,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X2] : (k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) ) | (~spl4_1 | ~spl4_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl4_1 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X2] : (~v1_funct_1(sK3) | k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_6),
% 0.21/0.48    inference(resolution,[],[f94,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl4_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) ) | (~spl4_1 | ~spl4_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f75])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(sK3) | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) ) | ~spl4_6),
% 0.21/0.48    inference(resolution,[],[f94,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    ( ! [X2] : (~v1_funct_1(k7_relat_1(sK3,X2)) | ~v1_relat_1(k7_relat_1(sK3,X2)) | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) ) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.21/0.48    inference(resolution,[],[f275,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f274,f124])).
% 0.21/0.48  fof(f274,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) ) | (~spl4_1 | ~spl4_6)),
% 0.21/0.48    inference(resolution,[],[f254,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    ( ! [X11] : (v5_relat_1(k7_relat_1(sK3,X11),sK1)) ) | (~spl4_1 | ~spl4_6)),
% 0.21/0.48    inference(forward_demodulation,[],[f237,f108])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    ( ! [X11] : (v5_relat_1(k2_partfun1(sK0,sK1,sK3,X11),sK1)) ) | (~spl4_1 | ~spl4_6)),
% 0.21/0.48    inference(resolution,[],[f107,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_1 | ~spl4_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f97,f75])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_funct_1(sK3) | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_6),
% 0.21/0.48    inference(resolution,[],[f94,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f504,plain,(
% 0.21/0.48    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_6 | spl4_8)),
% 0.21/0.48    inference(forward_demodulation,[],[f118,f108])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl4_8 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f498,plain,(
% 0.21/0.48    ~spl4_1 | ~spl4_6 | ~spl4_7 | spl4_29 | ~spl4_30),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f497])).
% 0.21/0.48  fof(f497,plain,(
% 0.21/0.48    $false | (~spl4_1 | ~spl4_6 | ~spl4_7 | spl4_29 | ~spl4_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f493,f485])).
% 0.21/0.48  fof(f485,plain,(
% 0.21/0.48    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f484])).
% 0.21/0.48  fof(f484,plain,(
% 0.21/0.48    spl4_29 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.48  fof(f493,plain,(
% 0.21/0.48    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_1 | ~spl4_6 | ~spl4_7 | ~spl4_30)),
% 0.21/0.48    inference(superposition,[],[f305,f489])).
% 0.21/0.48  fof(f305,plain,(
% 0.21/0.48    ( ! [X1] : (v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) ) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f304,f124])).
% 0.21/0.48  fof(f304,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_relat_1(k7_relat_1(sK3,X1)) | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) ) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f301,f228])).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_funct_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(k7_relat_1(sK3,X1)) | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) ) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.21/0.48    inference(resolution,[],[f275,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f490,plain,(
% 0.21/0.48    spl4_30 | ~spl4_2 | ~spl4_7 | ~spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f297,f142,f113,f78,f488])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl4_2 <=> r1_tarski(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    spl4_13 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_2 | ~spl4_7 | ~spl4_13)),
% 0.21/0.48    inference(resolution,[],[f165,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    r1_tarski(sK2,sK0) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | (~spl4_7 | ~spl4_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f164,f114])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_relat_1(sK3) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_13),
% 0.21/0.48    inference(superposition,[],[f55,f143])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK3) | ~spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f142])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.48  fof(f486,plain,(
% 0.21/0.48    ~spl4_29 | ~spl4_1 | ~spl4_6 | spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f481,f120,f93,f74,f484])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl4_9 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f481,plain,(
% 0.21/0.48    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_1 | ~spl4_6 | spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f121,f108])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f120])).
% 0.21/0.48  fof(f480,plain,(
% 0.21/0.48    sK3 != k7_relat_1(sK3,sK0) | k1_xboole_0 != sK0 | k1_xboole_0 != sK1 | v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f479,plain,(
% 0.21/0.48    sK3 != k7_relat_1(sK3,sK0) | k1_xboole_0 != sK2 | k1_xboole_0 != sK0 | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f478,plain,(
% 0.21/0.48    ~spl4_1 | ~spl4_6 | spl4_9 | ~spl4_20 | ~spl4_28),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f477])).
% 0.21/0.48  fof(f477,plain,(
% 0.21/0.48    $false | (~spl4_1 | ~spl4_6 | spl4_9 | ~spl4_20 | ~spl4_28)),
% 0.21/0.48    inference(subsumption_resolution,[],[f476,f390])).
% 0.21/0.48  fof(f390,plain,(
% 0.21/0.48    v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) | ~spl4_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f389])).
% 0.21/0.48  fof(f389,plain,(
% 0.21/0.48    spl4_28 <=> v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.48  fof(f476,plain,(
% 0.21/0.48    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) | (~spl4_1 | ~spl4_6 | spl4_9 | ~spl4_20)),
% 0.21/0.48    inference(forward_demodulation,[],[f475,f108])).
% 0.21/0.48  fof(f475,plain,(
% 0.21/0.48    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1) | (spl4_9 | ~spl4_20)),
% 0.21/0.48    inference(forward_demodulation,[],[f121,f208])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl4_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f207])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    spl4_20 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.48  fof(f271,plain,(
% 0.21/0.48    spl4_25 | ~spl4_7 | ~spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f138,f130,f113,f269])).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    spl4_25 <=> sK3 = k7_relat_1(sK3,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    spl4_11 <=> v4_relat_1(sK3,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    sK3 = k7_relat_1(sK3,sK0) | (~spl4_7 | ~spl4_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f137,f114])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK0) | ~spl4_11),
% 0.21/0.48    inference(resolution,[],[f131,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    v4_relat_1(sK3,sK0) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f130])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    spl4_20 | ~spl4_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f191,f161,f207])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl4_14 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.48  % (9151)Refutation not found, incomplete strategy% (9151)------------------------------
% 0.21/0.48  % (9151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9151)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9151)Memory used [KB]: 10618
% 0.21/0.48  % (9151)Time elapsed: 0.072 s
% 0.21/0.48  % (9151)------------------------------
% 0.21/0.48  % (9151)------------------------------
% 0.21/0.48  % (9154)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (9158)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (9152)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (9153)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (9163)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (9159)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | ~spl4_14),
% 0.21/0.49    inference(resolution,[],[f162,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    r1_tarski(sK2,k1_xboole_0) | ~spl4_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl4_14 | ~spl4_2 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f150,f86,f78,f161])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl4_4 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    r1_tarski(sK2,k1_xboole_0) | (~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(superposition,[],[f79,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl4_13 | ~spl4_3 | spl4_5 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f111,f93,f89,f82,f142])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl4_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl4_5 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK3) | (~spl4_3 | spl4_5 | ~spl4_6)),
% 0.21/0.49    inference(forward_demodulation,[],[f102,f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_3 | spl4_5 | ~spl4_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl4_5 | ~spl4_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f100,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f94,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f94,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl4_11 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f103,f93,f130])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    v4_relat_1(sK3,sK0) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f94,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ~spl4_10 | ~spl4_1 | ~spl4_6 | spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f123,f117,f93,f74,f126])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl4_10 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_6 | spl4_8)),
% 0.21/0.49    inference(forward_demodulation,[],[f118,f108])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ~spl4_8 | ~spl4_9 | ~spl4_1 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f106,f93,f74,f120,f117])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f36,f105])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f14])).
% 0.21/0.49  fof(f14,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl4_7 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f101,f93,f113])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f94,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f93])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl4_4 | ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f89,f86])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f82])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f78])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    r1_tarski(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f74])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (9164)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (9150)------------------------------
% 0.21/0.49  % (9150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9150)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (9150)Memory used [KB]: 6524
% 0.21/0.49  % (9150)Time elapsed: 0.067 s
% 0.21/0.49  % (9150)------------------------------
% 0.21/0.49  % (9150)------------------------------
% 0.21/0.49  % (9149)Success in time 0.142 s
%------------------------------------------------------------------------------
