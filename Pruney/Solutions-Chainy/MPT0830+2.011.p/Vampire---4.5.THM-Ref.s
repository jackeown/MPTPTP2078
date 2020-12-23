%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 155 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  190 ( 338 expanded)
%              Number of equality atoms :    3 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f103,f111,f122,f158])).

fof(f158,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl5_5 ),
    inference(resolution,[],[f155,f56])).

fof(f56,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(f155,plain,
    ( ! [X0] : ~ r1_tarski(sK3,k2_zfmisc_1(X0,sK2))
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f153,f55])).

fof(f55,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f29,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f153,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,k2_zfmisc_1(X0,sK2))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_5 ),
    inference(resolution,[],[f130,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k7_relat_1(sK3,sK1),X0)
        | ~ r1_tarski(X0,k2_zfmisc_1(X1,sK2)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f129,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f129,plain,
    ( ! [X2] : ~ r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(X2,sK2))
    | ~ spl5_5 ),
    inference(resolution,[],[f106,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f106,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_5
  <=> ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f122,plain,
    ( ~ spl5_2
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f120,f29])).

fof(f120,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f116,f110])).

fof(f110,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_6
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f116,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_2 ),
    inference(superposition,[],[f67,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f67,plain,
    ( r1_tarski(k1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1)),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_2
  <=> r1_tarski(k1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f111,plain,
    ( spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f89,f108,f105])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
      | ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    inference(resolution,[],[f70,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f70,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f61,f29])).

fof(f61,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(superposition,[],[f30,f49])).

fof(f30,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f101,f53])).

fof(f53,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f29,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f101,plain,
    ( ! [X0] : ~ v4_relat_1(sK3,X0)
    | spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f99,f55])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f97,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

fof(f97,plain,
    ( ~ v4_relat_1(k7_relat_1(sK3,sK1),sK1)
    | spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f95,f94])).

fof(f94,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f93,f29])).

fof(f93,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_4 ),
    inference(superposition,[],[f81,f49])).

fof(f81,plain,
    ( v1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_4
  <=> v1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f95,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v4_relat_1(k7_relat_1(sK3,sK1),sK1)
    | spl5_2 ),
    inference(resolution,[],[f84,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f84,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f74,f29])).

fof(f74,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_2 ),
    inference(superposition,[],[f68,f49])).

fof(f68,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1)),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f92,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f88,f53])).

fof(f88,plain,
    ( ! [X0] : ~ v4_relat_1(sK3,X0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f87,f55])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl5_4 ),
    inference(resolution,[],[f86,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | spl5_4 ),
    inference(subsumption_resolution,[],[f85,f29])).

fof(f85,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_4 ),
    inference(superposition,[],[f82,f49])).

fof(f82,plain,
    ( ~ v1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:07:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (7451)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (7465)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (7457)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (7468)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  % (7451)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f92,f103,f111,f122,f158])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    ~spl5_5),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f156])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    $false | ~spl5_5),
% 0.22/0.49    inference(resolution,[],[f155,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 0.22/0.49    inference(resolution,[],[f29,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.49    inference(negated_conjecture,[],[f13])).
% 0.22/0.49  fof(f13,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(sK3,k2_zfmisc_1(X0,sK2))) ) | ~spl5_5),
% 0.22/0.49    inference(subsumption_resolution,[],[f153,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    v1_relat_1(sK3)),
% 0.22/0.49    inference(resolution,[],[f29,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(sK3,k2_zfmisc_1(X0,sK2)) | ~v1_relat_1(sK3)) ) | ~spl5_5),
% 0.22/0.49    inference(resolution,[],[f130,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(k7_relat_1(sK3,sK1),X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,sK2))) ) | ~spl5_5),
% 0.22/0.49    inference(resolution,[],[f129,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ( ! [X2] : (~r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(X2,sK2))) ) | ~spl5_5),
% 0.22/0.49    inference(resolution,[],[f106,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | ~spl5_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f105])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl5_5 <=> ! [X0] : ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    ~spl5_2 | spl5_6),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f121])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    $false | (~spl5_2 | spl5_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f120,f29])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_2 | spl5_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f116,f110])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | spl5_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    spl5_6 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_2),
% 0.22/0.49    inference(superposition,[],[f67,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1)),sK1) | ~spl5_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl5_2 <=> r1_tarski(k1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1)),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    spl5_5 | ~spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f89,f108,f105])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 0.22/0.49    inference(resolution,[],[f70,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.49    inference(flattening,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f61,f29])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.49    inference(superposition,[],[f30,f49])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    spl5_2 | ~spl5_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f102])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    $false | (spl5_2 | ~spl5_4)),
% 0.22/0.49    inference(resolution,[],[f101,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    v4_relat_1(sK3,sK0)),
% 0.22/0.49    inference(resolution,[],[f29,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ( ! [X0] : (~v4_relat_1(sK3,X0)) ) | (spl5_2 | ~spl5_4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f99,f55])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | (spl5_2 | ~spl5_4)),
% 0.22/0.49    inference(resolution,[],[f97,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ~v4_relat_1(k7_relat_1(sK3,sK1),sK1) | (spl5_2 | ~spl5_4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f95,f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    v1_relat_1(k7_relat_1(sK3,sK1)) | ~spl5_4),
% 0.22/0.49    inference(subsumption_resolution,[],[f93,f29])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    v1_relat_1(k7_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_4),
% 0.22/0.49    inference(superposition,[],[f81,f49])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    v1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1)) | ~spl5_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl5_4 <=> v1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~v4_relat_1(k7_relat_1(sK3,sK1),sK1) | spl5_2),
% 0.22/0.49    inference(resolution,[],[f84,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | spl5_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f74,f29])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_2),
% 0.22/0.49    inference(superposition,[],[f68,f49])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ~r1_tarski(k1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1)),sK1) | spl5_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f66])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    spl5_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f91])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    $false | spl5_4),
% 0.22/0.49    inference(resolution,[],[f88,f53])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X0] : (~v4_relat_1(sK3,X0)) ) | spl5_4),
% 0.22/0.49    inference(subsumption_resolution,[],[f87,f55])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl5_4),
% 0.22/0.49    inference(resolution,[],[f86,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK3,sK1)) | spl5_4),
% 0.22/0.49    inference(subsumption_resolution,[],[f85,f29])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_4),
% 0.22/0.49    inference(superposition,[],[f82,f49])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ~v1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1)) | spl5_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (7451)------------------------------
% 0.22/0.49  % (7451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (7451)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (7451)Memory used [KB]: 10618
% 0.22/0.49  % (7451)Time elapsed: 0.063 s
% 0.22/0.49  % (7451)------------------------------
% 0.22/0.49  % (7451)------------------------------
% 0.22/0.50  % (7448)Success in time 0.132 s
%------------------------------------------------------------------------------
