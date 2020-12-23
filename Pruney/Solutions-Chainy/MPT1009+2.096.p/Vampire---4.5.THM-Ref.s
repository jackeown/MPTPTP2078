%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 125 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  219 ( 357 expanded)
%              Number of equality atoms :   58 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f70,f75,f82,f112,f124,f129,f138,f141])).

fof(f141,plain,
    ( ~ spl4_13
    | spl4_14 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl4_13
    | spl4_14 ),
    inference(subsumption_resolution,[],[f139,f122])).

fof(f122,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f139,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_14 ),
    inference(resolution,[],[f137,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f137,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_14
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f138,plain,
    ( ~ spl4_14
    | spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f130,f117,f109,f135])).

fof(f109,plain,
    ( spl4_11
  <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f117,plain,
    ( spl4_12
  <=> k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f130,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl4_11
    | ~ spl4_12 ),
    inference(superposition,[],[f111,f119])).

fof(f119,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f111,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f129,plain,
    ( ~ spl4_4
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl4_4
    | spl4_13 ),
    inference(resolution,[],[f125,f58])).

fof(f58,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f125,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_13 ),
    inference(resolution,[],[f123,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f123,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f124,plain,
    ( spl4_12
    | ~ spl4_13
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f115,f79,f41,f121,f117])).

fof(f41,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f79,plain,
    ( spl4_7
  <=> k1_tarski(sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f115,plain,
    ( ~ v1_relat_1(sK3)
    | k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f114,f43])).

fof(f43,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f114,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_7 ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != k1_relat_1(sK3)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,sK0)) )
    | ~ spl4_7 ),
    inference(superposition,[],[f25,f81])).

fof(f81,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_relat_1(X1) = k1_tarski(X0)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f112,plain,
    ( ~ spl4_11
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f76,f67,f56,f109])).

fof(f67,plain,
    ( spl4_5
  <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f76,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ spl4_4
    | spl4_5 ),
    inference(superposition,[],[f69,f60])).

fof(f60,plain,
    ( ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl4_4 ),
    inference(resolution,[],[f58,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f69,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f82,plain,
    ( spl4_7
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f77,f72,f56,f51,f46,f79])).

fof(f46,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f51,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f72,plain,
    ( spl4_6
  <=> k1_relset_1(k1_tarski(sK0),sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f77,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f65,f74])).

fof(f74,plain,
    ( k1_relset_1(k1_tarski(sK0),sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f65,plain,
    ( k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK3)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f64,f53])).

fof(f53,plain,
    ( v1_funct_2(sK3,k1_tarski(sK0),sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f64,plain,
    ( k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK3)
    | ~ v1_funct_2(sK3,k1_tarski(sK0),sK1)
    | spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f62,f48])).

fof(f48,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f62,plain,
    ( k1_xboole_0 = sK1
    | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK3)
    | ~ v1_funct_2(sK3,k1_tarski(sK0),sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f58,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f75,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f63,f56,f72])).

fof(f63,plain,
    ( k1_relset_1(k1_tarski(sK0),sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f58,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f70,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f23,f67])).

fof(f23,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f59,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f21,f56])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    v1_funct_2(sK3,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:26:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (13077)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (13071)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (13069)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (13066)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (13066)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f70,f75,f82,f112,f124,f129,f138,f141])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ~spl4_13 | spl4_14),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    $false | (~spl4_13 | spl4_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f139,f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl4_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl4_13 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | spl4_14),
% 0.21/0.49    inference(resolution,[],[f137,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | spl4_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f135])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl4_14 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ~spl4_14 | spl4_11 | ~spl4_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f130,f117,f109,f135])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl4_11 <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl4_12 <=> k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (spl4_11 | ~spl4_12)),
% 0.21/0.49    inference(superposition,[],[f111,f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f117])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl4_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f109])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ~spl4_4 | spl4_13),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    $false | (~spl4_4 | spl4_13)),
% 0.21/0.49    inference(resolution,[],[f125,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_13),
% 0.21/0.49    inference(resolution,[],[f123,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | spl4_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f121])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl4_12 | ~spl4_13 | ~spl4_1 | ~spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f115,f79,f41,f121,f117])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl4_1 <=> v1_funct_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl4_7 <=> k1_tarski(sK0) = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | (~spl4_1 | ~spl4_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f114,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v1_funct_1(sK3) | ~spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f41])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_7),
% 0.21/0.49    inference(equality_resolution,[],[f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X1] : (k1_relat_1(X1) != k1_relat_1(sK3) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,sK0))) ) | ~spl4_7),
% 0.21/0.49    inference(superposition,[],[f25,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    k1_tarski(sK0) = k1_relat_1(sK3) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(X1) != k1_tarski(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_relat_1(X1) != k1_tarski(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_relat_1(X1) != k1_tarski(X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_tarski(X0) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ~spl4_11 | ~spl4_4 | spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f76,f67,f56,f109])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl4_5 <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | (~spl4_4 | spl4_5)),
% 0.21/0.49    inference(superposition,[],[f69,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f58,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl4_7 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f77,f72,f56,f51,f46,f79])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl4_2 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl4_3 <=> v1_funct_2(sK3,k1_tarski(sK0),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl4_6 <=> k1_relset_1(k1_tarski(sK0),sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    k1_tarski(sK0) = k1_relat_1(sK3) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6)),
% 0.21/0.49    inference(forward_demodulation,[],[f65,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    k1_relset_1(k1_tarski(sK0),sK1,sK3) = k1_relat_1(sK3) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK3) | (spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f64,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    v1_funct_2(sK3,k1_tarski(sK0),sK1) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f51])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK3) | ~v1_funct_2(sK3,k1_tarski(sK0),sK1) | (spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f62,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f46])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK3) | ~v1_funct_2(sK3,k1_tarski(sK0),sK1) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f58,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl4_6 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f63,f56,f72])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    k1_relset_1(k1_tarski(sK0),sK1,sK3) = k1_relat_1(sK3) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f58,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f67])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f56])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f51])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    v1_funct_2(sK3,k1_tarski(sK0),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f46])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f41])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (13066)------------------------------
% 0.21/0.49  % (13066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13066)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (13066)Memory used [KB]: 10618
% 0.21/0.49  % (13066)Time elapsed: 0.075 s
% 0.21/0.49  % (13066)------------------------------
% 0.21/0.49  % (13066)------------------------------
% 0.21/0.49  % (13067)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (13060)Success in time 0.128 s
%------------------------------------------------------------------------------
