%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 204 expanded)
%              Number of leaves         :   32 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  305 ( 612 expanded)
%              Number of equality atoms :   35 (  51 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2766)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f519,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f82,f87,f101,f140,f185,f253,f254,f256,f330,f384,f385,f456,f515,f518])).

fof(f518,plain,(
    spl6_53 ),
    inference(avatar_split_clause,[],[f516,f505])).

fof(f505,plain,
    ( spl6_53
  <=> v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f516,plain,(
    v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f503,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f503,plain,(
    ! [X4] : ~ r2_hidden(X4,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f356,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f356,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[],[f355,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f355,plain,(
    ! [X0] : m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f354,f350])).

fof(f350,plain,(
    ! [X0] : k2_relat_1(k1_xboole_0) = k2_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(resolution,[],[f155,f122])).

fof(f122,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f121,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f121,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f155,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k2_relset_1(k1_xboole_0,X2,X3) = k2_relat_1(X3) ) ),
    inference(superposition,[],[f47,f52])).

fof(f52,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

% (2767)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (2758)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (2768)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (2765)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (2755)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (2761)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (2765)Refutation not found, incomplete strategy% (2765)------------------------------
% (2765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2766)Refutation not found, incomplete strategy% (2766)------------------------------
% (2766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2761)Refutation not found, incomplete strategy% (2761)------------------------------
% (2761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2761)Termination reason: Refutation not found, incomplete strategy

% (2761)Memory used [KB]: 10618
% (2761)Time elapsed: 0.147 s
% (2761)------------------------------
% (2761)------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f354,plain,(
    ! [X0] : m1_subset_1(k2_relset_1(k1_xboole_0,X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f164,f122])).

fof(f164,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | m1_subset_1(k2_relset_1(k1_xboole_0,X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f48,f52])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f515,plain,
    ( ~ spl6_13
    | ~ spl6_53 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | ~ spl6_13
    | ~ spl6_53 ),
    inference(resolution,[],[f507,f136])).

fof(f136,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_13
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f507,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f505])).

fof(f456,plain,
    ( k1_xboole_0 != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f385,plain,
    ( k3_funct_2(sK0,sK1,sK3,sK2) != k1_funct_1(sK3,sK2)
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f384,plain,
    ( spl6_43
    | ~ spl6_3
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f379,f178,f64,f381])).

fof(f381,plain,
    ( spl6_43
  <=> k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f64,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f178,plain,
    ( spl6_18
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f379,plain,
    ( k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2)
    | ~ spl6_3
    | ~ spl6_18 ),
    inference(resolution,[],[f179,f66])).

fof(f66,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f178])).

fof(f330,plain,
    ( spl6_38
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f323,f198,f157,f98,f327])).

fof(f327,plain,
    ( spl6_38
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f98,plain,
    ( spl6_9
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f157,plain,
    ( spl6_16
  <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f198,plain,
    ( spl6_21
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f323,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(resolution,[],[f322,f100])).

fof(f100,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) )
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f199,f159])).

fof(f159,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f157])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3)) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f198])).

fof(f256,plain,
    ( spl6_16
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f249,f74,f157])).

fof(f74,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f249,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f76,f47])).

fof(f76,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f254,plain,
    ( spl6_18
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f247,f74,f84,f79,f54,f178])).

fof(f54,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f79,plain,
    ( spl6_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f84,plain,
    ( spl6_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f247,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,sK1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,sK0)
        | k3_funct_2(sK0,sK1,sK3,X1) = k1_funct_1(sK3,X1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f76,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f253,plain,
    ( spl6_20
    | spl6_21
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f246,f74,f79,f84,f198,f194])).

fof(f194,plain,
    ( spl6_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK0,sK1)
        | ~ v1_funct_1(sK3)
        | ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = sK1
        | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f76,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f185,plain,
    ( spl6_15
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f150,f138,f142])).

fof(f142,plain,
    ( spl6_15
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f138,plain,
    ( spl6_14
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f150,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_14 ),
    inference(resolution,[],[f139,f122])).

fof(f139,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X1) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl6_13
    | spl6_14 ),
    inference(avatar_split_clause,[],[f132,f138,f135])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f36,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f101,plain,
    ( spl6_9
    | spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f95,f64,f54,f98])).

fof(f95,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK2,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f37,f66])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f87,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f27,f84])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X3,X0,X1)
                      & v1_funct_1(X3) )
                   => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

fof(f82,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f28,f79])).

fof(f28,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f77,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f29,f74])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f69,plain,
    ( spl6_4
  <=> r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f30,plain,(
    ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f31,f64])).

fof(f31,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f59,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f32,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f33,f54])).

fof(f33,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:48:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (2746)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.48  % (2746)Refutation not found, incomplete strategy% (2746)------------------------------
% 0.20/0.48  % (2746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (2746)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (2746)Memory used [KB]: 10746
% 0.20/0.49  % (2746)Time elapsed: 0.094 s
% 0.20/0.49  % (2746)------------------------------
% 0.20/0.49  % (2746)------------------------------
% 0.20/0.49  % (2770)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.49  % (2762)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (2745)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (2750)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (2748)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (2752)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (2744)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (2769)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (2759)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (2760)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (2751)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (2753)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (2772)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (2749)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (2747)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (2754)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (2760)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (2754)Refutation not found, incomplete strategy% (2754)------------------------------
% 0.20/0.53  % (2754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2754)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2754)Memory used [KB]: 10618
% 0.20/0.53  % (2754)Time elapsed: 0.115 s
% 0.20/0.53  % (2754)------------------------------
% 0.20/0.53  % (2754)------------------------------
% 0.20/0.53  % (2764)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (2756)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (2771)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (2763)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (2752)Refutation not found, incomplete strategy% (2752)------------------------------
% 0.20/0.54  % (2752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2752)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2752)Memory used [KB]: 10746
% 0.20/0.54  % (2752)Time elapsed: 0.136 s
% 0.20/0.54  % (2752)------------------------------
% 0.20/0.54  % (2752)------------------------------
% 0.20/0.54  % (2773)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  % (2766)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  fof(f519,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f82,f87,f101,f140,f185,f253,f254,f256,f330,f384,f385,f456,f515,f518])).
% 0.20/0.54  fof(f518,plain,(
% 0.20/0.54    spl6_53),
% 0.20/0.54    inference(avatar_split_clause,[],[f516,f505])).
% 0.20/0.54  fof(f505,plain,(
% 0.20/0.54    spl6_53 <=> v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.20/0.54  fof(f516,plain,(
% 0.20/0.54    v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 0.20/0.54    inference(resolution,[],[f503,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.54  fof(f503,plain,(
% 0.20/0.54    ( ! [X4] : (~r2_hidden(X4,k2_relat_1(k1_xboole_0))) )),
% 0.20/0.54    inference(resolution,[],[f356,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.54  fof(f356,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0)) )),
% 0.20/0.54    inference(resolution,[],[f355,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f355,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f354,f350])).
% 0.20/0.54  fof(f350,plain,(
% 0.20/0.54    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.20/0.54    inference(resolution,[],[f155,f122])).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(resolution,[],[f121,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f120])).
% 0.20/0.54  fof(f120,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.20/0.54    inference(resolution,[],[f40,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k2_relset_1(k1_xboole_0,X2,X3) = k2_relat_1(X3)) )),
% 0.20/0.54    inference(superposition,[],[f47,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  % (2767)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (2758)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (2768)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (2765)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (2755)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (2761)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (2765)Refutation not found, incomplete strategy% (2765)------------------------------
% 0.20/0.55  % (2765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2766)Refutation not found, incomplete strategy% (2766)------------------------------
% 0.20/0.55  % (2766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2761)Refutation not found, incomplete strategy% (2761)------------------------------
% 0.20/0.55  % (2761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2761)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2761)Memory used [KB]: 10618
% 0.20/0.55  % (2761)Time elapsed: 0.147 s
% 0.20/0.55  % (2761)------------------------------
% 0.20/0.55  % (2761)------------------------------
% 1.58/0.55  fof(f3,axiom,(
% 1.58/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.58/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.58/0.55  fof(f47,plain,(
% 1.58/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.58/0.55    inference(cnf_transformation,[],[f21])).
% 1.58/0.55  fof(f21,plain,(
% 1.58/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.55    inference(ennf_transformation,[],[f9])).
% 1.58/0.55  fof(f9,axiom,(
% 1.58/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.58/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.58/0.55  fof(f354,plain,(
% 1.58/0.55    ( ! [X0] : (m1_subset_1(k2_relset_1(k1_xboole_0,X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 1.58/0.55    inference(resolution,[],[f164,f122])).
% 1.58/0.55  fof(f164,plain,(
% 1.58/0.55    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k2_relset_1(k1_xboole_0,X2,X3),k1_zfmisc_1(X2))) )),
% 1.58/0.55    inference(superposition,[],[f48,f52])).
% 1.58/0.55  fof(f48,plain,(
% 1.58/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 1.58/0.55    inference(cnf_transformation,[],[f22])).
% 1.58/0.55  fof(f22,plain,(
% 1.58/0.55    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.55    inference(ennf_transformation,[],[f8])).
% 1.58/0.55  fof(f8,axiom,(
% 1.58/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.58/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.58/0.55  fof(f515,plain,(
% 1.58/0.55    ~spl6_13 | ~spl6_53),
% 1.58/0.55    inference(avatar_contradiction_clause,[],[f513])).
% 1.58/0.55  fof(f513,plain,(
% 1.58/0.55    $false | (~spl6_13 | ~spl6_53)),
% 1.58/0.55    inference(resolution,[],[f507,f136])).
% 1.58/0.55  fof(f136,plain,(
% 1.58/0.55    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl6_13),
% 1.58/0.55    inference(avatar_component_clause,[],[f135])).
% 1.58/0.55  fof(f135,plain,(
% 1.58/0.55    spl6_13 <=> ! [X0] : ~v1_xboole_0(X0)),
% 1.58/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.58/0.55  fof(f507,plain,(
% 1.58/0.55    v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl6_53),
% 1.58/0.55    inference(avatar_component_clause,[],[f505])).
% 1.58/0.56  fof(f456,plain,(
% 1.58/0.56    k1_xboole_0 != sK1 | v1_xboole_0(sK1) | ~v1_xboole_0(k1_xboole_0)),
% 1.58/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.58/0.56  fof(f385,plain,(
% 1.58/0.56    k3_funct_2(sK0,sK1,sK3,sK2) != k1_funct_1(sK3,sK2) | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3) | r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | ~r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 1.58/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.58/0.56  fof(f384,plain,(
% 1.58/0.56    spl6_43 | ~spl6_3 | ~spl6_18),
% 1.58/0.56    inference(avatar_split_clause,[],[f379,f178,f64,f381])).
% 1.58/0.56  fof(f381,plain,(
% 1.58/0.56    spl6_43 <=> k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2)),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 1.58/0.56  fof(f64,plain,(
% 1.58/0.56    spl6_3 <=> m1_subset_1(sK2,sK0)),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.58/0.56  fof(f178,plain,(
% 1.58/0.56    spl6_18 <=> ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0))),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.58/0.56  fof(f379,plain,(
% 1.58/0.56    k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2) | (~spl6_3 | ~spl6_18)),
% 1.58/0.56    inference(resolution,[],[f179,f66])).
% 1.58/0.56  fof(f66,plain,(
% 1.58/0.56    m1_subset_1(sK2,sK0) | ~spl6_3),
% 1.58/0.56    inference(avatar_component_clause,[],[f64])).
% 1.58/0.56  fof(f179,plain,(
% 1.58/0.56    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK3,X0) = k1_funct_1(sK3,X0)) ) | ~spl6_18),
% 1.58/0.56    inference(avatar_component_clause,[],[f178])).
% 1.58/0.56  fof(f330,plain,(
% 1.58/0.56    spl6_38 | ~spl6_9 | ~spl6_16 | ~spl6_21),
% 1.58/0.56    inference(avatar_split_clause,[],[f323,f198,f157,f98,f327])).
% 1.58/0.56  fof(f327,plain,(
% 1.58/0.56    spl6_38 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 1.58/0.56  fof(f98,plain,(
% 1.58/0.56    spl6_9 <=> r2_hidden(sK2,sK0)),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.58/0.56  fof(f157,plain,(
% 1.58/0.56    spl6_16 <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.58/0.56  fof(f198,plain,(
% 1.58/0.56    spl6_21 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3)))),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.58/0.56  fof(f323,plain,(
% 1.58/0.56    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | (~spl6_9 | ~spl6_16 | ~spl6_21)),
% 1.58/0.56    inference(resolution,[],[f322,f100])).
% 1.58/0.56  fof(f100,plain,(
% 1.58/0.56    r2_hidden(sK2,sK0) | ~spl6_9),
% 1.58/0.56    inference(avatar_component_clause,[],[f98])).
% 1.58/0.56  fof(f322,plain,(
% 1.58/0.56    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) ) | (~spl6_16 | ~spl6_21)),
% 1.58/0.56    inference(forward_demodulation,[],[f199,f159])).
% 1.58/0.56  fof(f159,plain,(
% 1.58/0.56    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl6_16),
% 1.58/0.56    inference(avatar_component_clause,[],[f157])).
% 1.58/0.56  fof(f199,plain,(
% 1.58/0.56    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3))) ) | ~spl6_21),
% 1.58/0.56    inference(avatar_component_clause,[],[f198])).
% 1.58/0.56  fof(f256,plain,(
% 1.58/0.56    spl6_16 | ~spl6_5),
% 1.58/0.56    inference(avatar_split_clause,[],[f249,f74,f157])).
% 1.58/0.56  fof(f74,plain,(
% 1.58/0.56    spl6_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.58/0.56  fof(f249,plain,(
% 1.58/0.56    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl6_5),
% 1.58/0.56    inference(resolution,[],[f76,f47])).
% 1.58/0.56  fof(f76,plain,(
% 1.58/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_5),
% 1.58/0.56    inference(avatar_component_clause,[],[f74])).
% 1.58/0.56  fof(f254,plain,(
% 1.58/0.56    spl6_18 | spl6_1 | ~spl6_6 | ~spl6_7 | ~spl6_5),
% 1.58/0.56    inference(avatar_split_clause,[],[f247,f74,f84,f79,f54,f178])).
% 1.58/0.56  fof(f54,plain,(
% 1.58/0.56    spl6_1 <=> v1_xboole_0(sK0)),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.58/0.56  fof(f79,plain,(
% 1.58/0.56    spl6_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.58/0.56  fof(f84,plain,(
% 1.58/0.56    spl6_7 <=> v1_funct_1(sK3)),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.58/0.56  fof(f247,plain,(
% 1.58/0.56    ( ! [X1] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK1) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK1,sK3,X1) = k1_funct_1(sK3,X1)) ) | ~spl6_5),
% 1.58/0.56    inference(resolution,[],[f76,f49])).
% 1.58/0.56  fof(f49,plain,(
% 1.58/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f24])).
% 1.58/0.56  fof(f24,plain,(
% 1.58/0.56    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.58/0.56    inference(flattening,[],[f23])).
% 1.58/0.56  fof(f23,plain,(
% 1.58/0.56    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.58/0.56    inference(ennf_transformation,[],[f10])).
% 1.58/0.56  fof(f10,axiom,(
% 1.58/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.58/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.58/0.56  fof(f253,plain,(
% 1.58/0.56    spl6_20 | spl6_21 | ~spl6_7 | ~spl6_6 | ~spl6_5),
% 1.58/0.56    inference(avatar_split_clause,[],[f246,f74,f79,f84,f198,f194])).
% 1.58/0.56  fof(f194,plain,(
% 1.58/0.56    spl6_20 <=> k1_xboole_0 = sK1),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.58/0.56  fof(f246,plain,(
% 1.58/0.56    ( ! [X0] : (~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK0,sK1,sK3))) ) | ~spl6_5),
% 1.58/0.56    inference(resolution,[],[f76,f50])).
% 1.58/0.56  fof(f50,plain,(
% 1.58/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 1.58/0.56    inference(cnf_transformation,[],[f26])).
% 1.58/0.56  fof(f26,plain,(
% 1.58/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.58/0.56    inference(flattening,[],[f25])).
% 1.58/0.56  fof(f25,plain,(
% 1.58/0.56    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.58/0.56    inference(ennf_transformation,[],[f11])).
% 1.58/0.56  fof(f11,axiom,(
% 1.58/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.58/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 1.58/0.56  fof(f185,plain,(
% 1.58/0.56    spl6_15 | ~spl6_14),
% 1.58/0.56    inference(avatar_split_clause,[],[f150,f138,f142])).
% 1.58/0.56  fof(f142,plain,(
% 1.58/0.56    spl6_15 <=> v1_xboole_0(k1_xboole_0)),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.58/0.56  fof(f138,plain,(
% 1.58/0.56    spl6_14 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X1))),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.58/0.56  fof(f150,plain,(
% 1.58/0.56    v1_xboole_0(k1_xboole_0) | ~spl6_14),
% 1.58/0.56    inference(resolution,[],[f139,f122])).
% 1.58/0.56  fof(f139,plain,(
% 1.58/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X1)) ) | ~spl6_14),
% 1.58/0.56    inference(avatar_component_clause,[],[f138])).
% 1.58/0.56  fof(f140,plain,(
% 1.58/0.56    spl6_13 | spl6_14),
% 1.58/0.56    inference(avatar_split_clause,[],[f132,f138,f135])).
% 1.58/0.56  fof(f132,plain,(
% 1.58/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 1.58/0.56    inference(superposition,[],[f36,f51])).
% 1.58/0.56  fof(f51,plain,(
% 1.58/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.58/0.56    inference(equality_resolution,[],[f45])).
% 1.58/0.56  fof(f45,plain,(
% 1.58/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.58/0.56    inference(cnf_transformation,[],[f3])).
% 1.58/0.56  fof(f36,plain,(
% 1.58/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f16])).
% 1.58/0.56  fof(f16,plain,(
% 1.58/0.56    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.58/0.56    inference(ennf_transformation,[],[f7])).
% 1.58/0.56  fof(f7,axiom,(
% 1.58/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.58/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.58/0.56  fof(f101,plain,(
% 1.58/0.56    spl6_9 | spl6_1 | ~spl6_3),
% 1.58/0.56    inference(avatar_split_clause,[],[f95,f64,f54,f98])).
% 1.58/0.56  fof(f95,plain,(
% 1.58/0.56    v1_xboole_0(sK0) | r2_hidden(sK2,sK0) | ~spl6_3),
% 1.58/0.56    inference(resolution,[],[f37,f66])).
% 1.58/0.56  fof(f37,plain,(
% 1.58/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f18])).
% 1.58/0.56  fof(f18,plain,(
% 1.58/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.58/0.56    inference(flattening,[],[f17])).
% 1.58/0.56  fof(f17,plain,(
% 1.58/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.58/0.56    inference(ennf_transformation,[],[f4])).
% 1.58/0.56  fof(f4,axiom,(
% 1.58/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.58/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.58/0.56  fof(f87,plain,(
% 1.58/0.56    spl6_7),
% 1.58/0.56    inference(avatar_split_clause,[],[f27,f84])).
% 1.58/0.56  fof(f27,plain,(
% 1.58/0.56    v1_funct_1(sK3)),
% 1.58/0.56    inference(cnf_transformation,[],[f15])).
% 1.58/0.56  fof(f15,plain,(
% 1.58/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.58/0.56    inference(flattening,[],[f14])).
% 1.58/0.56  fof(f14,plain,(
% 1.58/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.58/0.56    inference(ennf_transformation,[],[f13])).
% 1.58/0.56  fof(f13,negated_conjecture,(
% 1.58/0.56    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 1.58/0.56    inference(negated_conjecture,[],[f12])).
% 1.58/0.56  fof(f12,conjecture,(
% 1.58/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 1.58/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).
% 1.58/0.56  fof(f82,plain,(
% 1.58/0.56    spl6_6),
% 1.58/0.56    inference(avatar_split_clause,[],[f28,f79])).
% 1.58/0.56  fof(f28,plain,(
% 1.58/0.56    v1_funct_2(sK3,sK0,sK1)),
% 1.58/0.56    inference(cnf_transformation,[],[f15])).
% 1.58/0.56  fof(f77,plain,(
% 1.58/0.56    spl6_5),
% 1.58/0.56    inference(avatar_split_clause,[],[f29,f74])).
% 1.58/0.56  fof(f29,plain,(
% 1.58/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.58/0.56    inference(cnf_transformation,[],[f15])).
% 1.58/0.56  fof(f72,plain,(
% 1.58/0.56    ~spl6_4),
% 1.58/0.56    inference(avatar_split_clause,[],[f30,f69])).
% 1.58/0.56  fof(f69,plain,(
% 1.58/0.56    spl6_4 <=> r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.58/0.56  fof(f30,plain,(
% 1.58/0.56    ~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 1.58/0.56    inference(cnf_transformation,[],[f15])).
% 1.58/0.56  fof(f67,plain,(
% 1.58/0.56    spl6_3),
% 1.58/0.56    inference(avatar_split_clause,[],[f31,f64])).
% 1.58/0.56  fof(f31,plain,(
% 1.58/0.56    m1_subset_1(sK2,sK0)),
% 1.58/0.56    inference(cnf_transformation,[],[f15])).
% 1.58/0.56  fof(f62,plain,(
% 1.58/0.56    ~spl6_2),
% 1.58/0.56    inference(avatar_split_clause,[],[f32,f59])).
% 1.58/0.56  fof(f59,plain,(
% 1.58/0.56    spl6_2 <=> v1_xboole_0(sK1)),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.58/0.56  fof(f32,plain,(
% 1.58/0.56    ~v1_xboole_0(sK1)),
% 1.58/0.56    inference(cnf_transformation,[],[f15])).
% 1.58/0.56  fof(f57,plain,(
% 1.58/0.56    ~spl6_1),
% 1.58/0.56    inference(avatar_split_clause,[],[f33,f54])).
% 1.58/0.56  fof(f33,plain,(
% 1.58/0.56    ~v1_xboole_0(sK0)),
% 1.58/0.56    inference(cnf_transformation,[],[f15])).
% 1.58/0.56  % SZS output end Proof for theBenchmark
% 1.58/0.56  % (2760)------------------------------
% 1.58/0.56  % (2760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (2760)Termination reason: Refutation
% 1.58/0.56  
% 1.58/0.56  % (2760)Memory used [KB]: 11001
% 1.58/0.56  % (2760)Time elapsed: 0.132 s
% 1.58/0.56  % (2760)------------------------------
% 1.58/0.56  % (2760)------------------------------
% 1.58/0.56  % (2743)Success in time 0.203 s
%------------------------------------------------------------------------------
