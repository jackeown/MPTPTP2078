%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 261 expanded)
%              Number of leaves         :   17 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  232 ( 760 expanded)
%              Number of equality atoms :   59 ( 168 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f141,f148,f312,f316,f354])).

fof(f354,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f95,f319,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f319,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f221,f307])).

fof(f307,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl4_5
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f221,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f201,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f201,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f80,f196])).

fof(f196,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f171,f34])).

fof(f171,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f44,f152,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

% (11146)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f20,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f152,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_xboole_0))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f63,f140])).

% (11136)Refutation not found, incomplete strategy% (11136)------------------------------
% (11136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11136)Termination reason: Refutation not found, incomplete strategy

% (11136)Memory used [KB]: 10746
% (11136)Time elapsed: 0.107 s
% (11136)------------------------------
% (11136)------------------------------
fof(f140,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f63,plain,(
    ~ v1_xboole_0(k1_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f28,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f80,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_2
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f95,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f89,f90])).

fof(f90,plain,(
    k1_xboole_0 = k1_funct_2(k1_funct_2(sK0,sK1),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f67,f34])).

fof(f67,plain,(
    v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f44,f63,f41])).

fof(f89,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_funct_2(k1_funct_2(sK0,sK1),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f67,f40])).

fof(f316,plain,
    ( ~ spl4_4
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl4_4
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f161,f311])).

fof(f311,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f161,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f151,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f62,f140])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f28,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f312,plain,
    ( spl4_5
    | ~ spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f246,f138,f309,f305])).

fof(f246,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f245,f51])).

fof(f245,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f242,f206])).

fof(f206,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f155,f196])).

fof(f155,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f71,f140])).

fof(f71,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f62,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f242,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f203,f53])).

fof(f53,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f203,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f150,f196])).

fof(f150,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f61,f140])).

fof(f61,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f148,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f28,f136,f38])).

fof(f136,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f141,plain,
    ( ~ spl4_3
    | spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f72,f78,f138,f134])).

fof(f72,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f66,f71])).

fof(f66,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f61,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f26,f70,f76,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f76,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_1
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f70,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f62,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f25,f78,f74])).

fof(f25,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:14:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (11138)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (11163)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.50  % (11137)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (11160)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (11134)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (11147)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (11138)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (11136)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f358,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f81,f86,f141,f148,f312,f316,f354])).
% 0.21/0.52  fof(f354,plain,(
% 0.21/0.52    spl4_2 | ~spl4_4 | ~spl4_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f349])).
% 0.21/0.52  fof(f349,plain,(
% 0.21/0.52    $false | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f95,f319,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 0.21/0.52    inference(backward_demodulation,[],[f221,f307])).
% 0.21/0.52  fof(f307,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(sK2) | ~spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f305])).
% 0.21/0.52  fof(f305,plain,(
% 0.21/0.52    spl4_5 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_relat_1(sK2)) | (spl4_2 | ~spl4_4)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f201,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(sK2) | (spl4_2 | ~spl4_4)),
% 0.21/0.52    inference(backward_demodulation,[],[f80,f196])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl4_4),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f171,f34])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    v1_xboole_0(sK0) | ~spl4_4),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f44,f152,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(X0) | v1_xboole_0(k1_funct_2(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  % (11146)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_funct_2(sK0,k1_xboole_0)) | ~spl4_4),
% 0.21/0.52    inference(backward_demodulation,[],[f63,f140])).
% 0.21/0.52  % (11136)Refutation not found, incomplete strategy% (11136)------------------------------
% 0.21/0.52  % (11136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11136)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11136)Memory used [KB]: 10746
% 0.21/0.52  % (11136)Time elapsed: 0.107 s
% 0.21/0.52  % (11136)------------------------------
% 0.21/0.52  % (11136)------------------------------
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f138])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    spl4_4 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_funct_2(sK0,sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f28,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    sK0 != k1_relat_1(sK2) | spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl4_2 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f89,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    k1_xboole_0 = k1_funct_2(k1_funct_2(sK0,sK1),k1_xboole_0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f67,f34])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_xboole_0))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f44,f63,f41])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_funct_2(k1_funct_2(sK0,sK1),k1_xboole_0))) )),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f67,f40])).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    ~spl4_4 | spl4_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f313])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    $false | (~spl4_4 | spl4_6)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f161,f311])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl4_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f309])).
% 0.21/0.52  fof(f309,plain,(
% 0.21/0.52    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_4),
% 0.21/0.52    inference(forward_demodulation,[],[f151,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl4_4),
% 0.21/0.52    inference(backward_demodulation,[],[f62,f140])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f28,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_funct_2(X0,X1)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    spl4_5 | ~spl4_6 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f246,f138,f309,f305])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2) | ~spl4_4),
% 0.21/0.52    inference(forward_demodulation,[],[f245,f51])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_4),
% 0.21/0.52    inference(forward_demodulation,[],[f242,f206])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~spl4_4),
% 0.21/0.52    inference(backward_demodulation,[],[f155,f196])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) | ~spl4_4),
% 0.21/0.52    inference(backward_demodulation,[],[f71,f140])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f62,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f203,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl4_4),
% 0.21/0.52    inference(backward_demodulation,[],[f150,f196])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl4_4),
% 0.21/0.52    inference(backward_demodulation,[],[f61,f140])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f28,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_funct_2(X0,X1)) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    spl4_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f144])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    $false | spl4_3),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f28,f136,f38])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f134])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ~spl4_3 | spl4_4 | spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f72,f78,f138,f134])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(backward_demodulation,[],[f66,f71])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(resolution,[],[f61,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl4_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    $false | spl4_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f26,f70,f76,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK2),sK1) | spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl4_1 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    v5_relat_1(sK2,sK1)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f62,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ~spl4_1 | ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f25,f78,f74])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    sK0 != k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (11138)------------------------------
% 0.21/0.52  % (11138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11138)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (11138)Memory used [KB]: 6268
% 0.21/0.52  % (11138)Time elapsed: 0.096 s
% 0.21/0.52  % (11138)------------------------------
% 0.21/0.52  % (11138)------------------------------
% 0.21/0.52  % (11130)Success in time 0.157 s
%------------------------------------------------------------------------------
