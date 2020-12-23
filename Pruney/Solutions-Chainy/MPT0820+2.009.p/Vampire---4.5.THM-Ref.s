%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 134 expanded)
%              Number of leaves         :   24 (  59 expanded)
%              Depth                    :    6
%              Number of atoms          :  248 ( 358 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f45,f53,f61,f65,f69,f73,f77,f83,f93,f99,f105,f111,f126,f143,f148])).

fof(f148,plain,
    ( ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13
    | spl3_19 ),
    inference(subsumption_resolution,[],[f146,f82])).

fof(f82,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f146,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_13
    | spl3_19 ),
    inference(subsumption_resolution,[],[f145,f92])).

fof(f92,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_13
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f145,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_19 ),
    inference(resolution,[],[f125,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f125,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_19
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f143,plain,
    ( ~ spl3_7
    | ~ spl3_12
    | ~ spl3_14
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_14
    | spl3_18 ),
    inference(subsumption_resolution,[],[f141,f82])).

fof(f141,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_7
    | ~ spl3_14
    | spl3_18 ),
    inference(subsumption_resolution,[],[f140,f98])).

fof(f98,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_14
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f140,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_7
    | spl3_18 ),
    inference(resolution,[],[f121,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f121,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_18
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f126,plain,
    ( ~ spl3_18
    | ~ spl3_19
    | spl3_1
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f116,f109,f33,f123,f119])).

fof(f33,plain,
    ( spl3_1
  <=> r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f109,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( r1_tarski(k3_relat_1(sK2),k2_xboole_0(X0,X1))
        | ~ r1_tarski(k2_relat_1(sK2),X1)
        | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f116,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_1
    | ~ spl3_16 ),
    inference(resolution,[],[f110,f35])).

fof(f35,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_relat_1(sK2),k2_xboole_0(X0,X1))
        | ~ r1_tarski(k2_relat_1(sK2),X1)
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f111,plain,
    ( spl3_16
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f106,f102,f75,f109])).

fof(f75,plain,
    ( spl3_11
  <=> ! [X1,X3,X0,X2] :
        ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f102,plain,
    ( spl3_15
  <=> k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_relat_1(sK2),k2_xboole_0(X0,X1))
        | ~ r1_tarski(k2_relat_1(sK2),X1)
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(superposition,[],[f76,f104])).

fof(f104,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f76,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f75])).

fof(f105,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f100,f80,f43,f102])).

fof(f43,plain,
    ( spl3_3
  <=> ! [X0] :
        ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f100,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(resolution,[],[f44,f82])).

fof(f44,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f99,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f94,f71,f38,f96])).

fof(f38,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f71,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f94,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(resolution,[],[f72,f40])).

fof(f40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f93,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f88,f67,f38,f90])).

fof(f67,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f88,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f68,f40])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f83,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f78,f63,f38,f80])).

fof(f63,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f78,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f64,f40])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f77,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f73,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f69,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f61,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f53,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f23,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

% (6890)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(f36,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f33])).

fof(f22,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:42:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (6895)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.41  % (6895)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f149,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f36,f41,f45,f53,f61,f65,f69,f73,f77,f83,f93,f99,f105,f111,f126,f143,f148])).
% 0.20/0.41  fof(f148,plain,(
% 0.20/0.41    ~spl3_5 | ~spl3_12 | ~spl3_13 | spl3_19),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f147])).
% 0.20/0.41  fof(f147,plain,(
% 0.20/0.41    $false | (~spl3_5 | ~spl3_12 | ~spl3_13 | spl3_19)),
% 0.20/0.41    inference(subsumption_resolution,[],[f146,f82])).
% 0.20/0.41  fof(f82,plain,(
% 0.20/0.41    v1_relat_1(sK2) | ~spl3_12),
% 0.20/0.41    inference(avatar_component_clause,[],[f80])).
% 0.20/0.41  fof(f80,plain,(
% 0.20/0.41    spl3_12 <=> v1_relat_1(sK2)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.41  fof(f146,plain,(
% 0.20/0.41    ~v1_relat_1(sK2) | (~spl3_5 | ~spl3_13 | spl3_19)),
% 0.20/0.41    inference(subsumption_resolution,[],[f145,f92])).
% 0.20/0.41  fof(f92,plain,(
% 0.20/0.41    v5_relat_1(sK2,sK1) | ~spl3_13),
% 0.20/0.41    inference(avatar_component_clause,[],[f90])).
% 0.20/0.41  fof(f90,plain,(
% 0.20/0.41    spl3_13 <=> v5_relat_1(sK2,sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.41  fof(f145,plain,(
% 0.20/0.41    ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (~spl3_5 | spl3_19)),
% 0.20/0.41    inference(resolution,[],[f125,f52])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_5),
% 0.20/0.41    inference(avatar_component_clause,[],[f51])).
% 0.20/0.41  fof(f51,plain,(
% 0.20/0.41    spl3_5 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.41  fof(f125,plain,(
% 0.20/0.41    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_19),
% 0.20/0.41    inference(avatar_component_clause,[],[f123])).
% 0.20/0.41  fof(f123,plain,(
% 0.20/0.41    spl3_19 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.41  fof(f143,plain,(
% 0.20/0.41    ~spl3_7 | ~spl3_12 | ~spl3_14 | spl3_18),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f142])).
% 0.20/0.41  fof(f142,plain,(
% 0.20/0.41    $false | (~spl3_7 | ~spl3_12 | ~spl3_14 | spl3_18)),
% 0.20/0.41    inference(subsumption_resolution,[],[f141,f82])).
% 0.20/0.41  fof(f141,plain,(
% 0.20/0.41    ~v1_relat_1(sK2) | (~spl3_7 | ~spl3_14 | spl3_18)),
% 0.20/0.41    inference(subsumption_resolution,[],[f140,f98])).
% 0.20/0.41  fof(f98,plain,(
% 0.20/0.41    v4_relat_1(sK2,sK0) | ~spl3_14),
% 0.20/0.41    inference(avatar_component_clause,[],[f96])).
% 0.20/0.41  fof(f96,plain,(
% 0.20/0.41    spl3_14 <=> v4_relat_1(sK2,sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.41  fof(f140,plain,(
% 0.20/0.41    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | (~spl3_7 | spl3_18)),
% 0.20/0.41    inference(resolution,[],[f121,f60])).
% 0.20/0.41  fof(f60,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_7),
% 0.20/0.41    inference(avatar_component_clause,[],[f59])).
% 0.20/0.41  fof(f59,plain,(
% 0.20/0.41    spl3_7 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.41  fof(f121,plain,(
% 0.20/0.41    ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_18),
% 0.20/0.41    inference(avatar_component_clause,[],[f119])).
% 0.20/0.42  fof(f119,plain,(
% 0.20/0.42    spl3_18 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.42  fof(f126,plain,(
% 0.20/0.42    ~spl3_18 | ~spl3_19 | spl3_1 | ~spl3_16),
% 0.20/0.42    inference(avatar_split_clause,[],[f116,f109,f33,f123,f119])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl3_1 <=> r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f109,plain,(
% 0.20/0.42    spl3_16 <=> ! [X1,X0] : (r1_tarski(k3_relat_1(sK2),k2_xboole_0(X0,X1)) | ~r1_tarski(k2_relat_1(sK2),X1) | ~r1_tarski(k1_relat_1(sK2),X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.42  fof(f116,plain,(
% 0.20/0.42    ~r1_tarski(k2_relat_1(sK2),sK1) | ~r1_tarski(k1_relat_1(sK2),sK0) | (spl3_1 | ~spl3_16)),
% 0.20/0.42    inference(resolution,[],[f110,f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) | spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f33])).
% 0.20/0.42  fof(f110,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k3_relat_1(sK2),k2_xboole_0(X0,X1)) | ~r1_tarski(k2_relat_1(sK2),X1) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | ~spl3_16),
% 0.20/0.42    inference(avatar_component_clause,[],[f109])).
% 0.20/0.42  fof(f111,plain,(
% 0.20/0.42    spl3_16 | ~spl3_11 | ~spl3_15),
% 0.20/0.42    inference(avatar_split_clause,[],[f106,f102,f75,f109])).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    spl3_11 <=> ! [X1,X3,X0,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.42  fof(f102,plain,(
% 0.20/0.42    spl3_15 <=> k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.42  fof(f106,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k3_relat_1(sK2),k2_xboole_0(X0,X1)) | ~r1_tarski(k2_relat_1(sK2),X1) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | (~spl3_11 | ~spl3_15)),
% 0.20/0.42    inference(superposition,[],[f76,f104])).
% 0.20/0.42  fof(f104,plain,(
% 0.20/0.42    k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_15),
% 0.20/0.42    inference(avatar_component_clause,[],[f102])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f75])).
% 0.20/0.42  fof(f105,plain,(
% 0.20/0.42    spl3_15 | ~spl3_3 | ~spl3_12),
% 0.20/0.42    inference(avatar_split_clause,[],[f100,f80,f43,f102])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl3_3 <=> ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f100,plain,(
% 0.20/0.42    k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_12)),
% 0.20/0.42    inference(resolution,[],[f44,f82])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) ) | ~spl3_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f43])).
% 0.20/0.42  fof(f99,plain,(
% 0.20/0.42    spl3_14 | ~spl3_2 | ~spl3_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f94,f71,f38,f96])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    spl3_10 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.42  fof(f94,plain,(
% 0.20/0.42    v4_relat_1(sK2,sK0) | (~spl3_2 | ~spl3_10)),
% 0.20/0.42    inference(resolution,[],[f72,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f38])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl3_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f71])).
% 0.20/0.42  fof(f93,plain,(
% 0.20/0.42    spl3_13 | ~spl3_2 | ~spl3_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f88,f67,f38,f90])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    spl3_9 <=> ! [X1,X0,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    v5_relat_1(sK2,sK1) | (~spl3_2 | ~spl3_9)),
% 0.20/0.42    inference(resolution,[],[f68,f40])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) ) | ~spl3_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f67])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    spl3_12 | ~spl3_2 | ~spl3_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f78,f63,f38,f80])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    spl3_8 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    v1_relat_1(sK2) | (~spl3_2 | ~spl3_8)),
% 0.20/0.42    inference(resolution,[],[f64,f40])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl3_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f63])).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    spl3_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f31,f75])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(flattening,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    spl3_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f29,f71])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    spl3_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f30,f67])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    spl3_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f28,f63])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl3_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f59])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(nnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl3_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f51])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(nnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl3_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f43])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f38])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  % (6890)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.20/0.42    inference(negated_conjecture,[],[f7])).
% 0.20/0.42  fof(f7,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ~spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f33])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (6895)------------------------------
% 0.20/0.42  % (6895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (6895)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (6895)Memory used [KB]: 6140
% 0.20/0.42  % (6895)Time elapsed: 0.006 s
% 0.20/0.42  % (6895)------------------------------
% 0.20/0.42  % (6895)------------------------------
% 0.20/0.42  % (6886)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.42  % (6884)Success in time 0.058 s
%------------------------------------------------------------------------------
