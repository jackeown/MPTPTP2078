%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 256 expanded)
%              Number of leaves         :   33 ( 102 expanded)
%              Depth                    :   16
%              Number of atoms          :  399 ( 773 expanded)
%              Number of equality atoms :  128 ( 255 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10040)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f458,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f78,f83,f92,f97,f102,f115,f122,f139,f146,f170,f193,f217,f233,f287,f358,f367,f457])).

fof(f457,plain,
    ( ~ spl3_6
    | spl3_15
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f456])).

fof(f456,plain,
    ( $false
    | ~ spl3_6
    | spl3_15
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f455,f34])).

fof(f34,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f455,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl3_6
    | spl3_15
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f278,f329])).

fof(f329,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl3_34
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f278,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl3_6
    | spl3_15 ),
    inference(superposition,[],[f145,f87])).

fof(f87,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_6
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f145,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_15
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f367,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2))
    | k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2))
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f358,plain,
    ( spl3_34
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f357,f166,f327])).

fof(f166,plain,
    ( spl3_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f357,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f356,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f356,plain,
    ( sK2 = k9_relat_1(k1_xboole_0,sK2)
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f355,f33])).

fof(f33,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f355,plain,
    ( sK2 = k9_relat_1(k6_relat_1(k1_xboole_0),sK2)
    | ~ spl3_18 ),
    inference(resolution,[],[f167,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f167,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f287,plain,
    ( ~ spl3_6
    | ~ spl3_10
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_10
    | spl3_18 ),
    inference(subsumption_resolution,[],[f285,f168])).

fof(f168,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f285,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f272,f52])).

fof(f52,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f272,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(superposition,[],[f114,f87])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f233,plain,
    ( spl3_25
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f226,f190,f112,f94,f89,f80,f75,f55,f230])).

fof(f230,plain,
    ( spl3_25
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f55,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f75,plain,
    ( spl3_4
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f80,plain,
    ( spl3_5
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f89,plain,
    ( spl3_7
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f94,plain,
    ( spl3_8
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f190,plain,
    ( spl3_19
  <=> k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f226,plain,
    ( k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | spl3_7
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f180,f192])).

fof(f192,plain,
    ( k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f190])).

fof(f180,plain,
    ( k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k9_relat_1(sK2,k2_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f179,f116])).

fof(f116,plain,
    ( ! [X0] : k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl3_10 ),
    inference(resolution,[],[f114,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f179,plain,
    ( k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f178,f82])).

fof(f82,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f178,plain,
    ( k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f177,f96])).

fof(f96,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f177,plain,
    ( u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f176,f91])).

fof(f91,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f176,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f175,f82])).

fof(f175,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f174,f114])).

fof(f174,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f173,f96])).

fof(f173,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f171,f82])).

fof(f171,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(resolution,[],[f69,f77])).

fof(f77,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k8_relset_1(X0,X1,sK2,k7_relset_1(X0,X1,sK2,X0)) = X0 )
    | ~ spl3_1 ),
    inference(resolution,[],[f57,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).

fof(f57,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f217,plain,
    ( spl3_23
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f210,f190,f112,f214])).

fof(f214,plain,
    ( spl3_23
  <=> k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f210,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2))
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f154,f192])).

fof(f154,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k9_relat_1(sK2,k2_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f149,f114])).

fof(f149,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k9_relat_1(sK2,k2_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_10 ),
    inference(superposition,[],[f47,f116])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

fof(f193,plain,
    ( spl3_19
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f186,f158,f112,f190])).

fof(f158,plain,
    ( spl3_16
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k9_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f186,plain,
    ( k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2)
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f184,f114])).

fof(f184,plain,
    ( k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_16 ),
    inference(superposition,[],[f160,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f160,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k9_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f158])).

fof(f170,plain,
    ( spl3_16
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f155,f112,f158])).

fof(f155,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k9_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f150,f114])).

fof(f150,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k9_relat_1(sK2,k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_10 ),
    inference(superposition,[],[f44,f116])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f146,plain,
    ( ~ spl3_15
    | ~ spl3_10
    | spl3_14 ),
    inference(avatar_split_clause,[],[f141,f136,f112,f143])).

fof(f136,plain,
    ( spl3_14
  <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f141,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ spl3_10
    | spl3_14 ),
    inference(subsumption_resolution,[],[f140,f114])).

fof(f140,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_14 ),
    inference(superposition,[],[f138,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f138,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,
    ( ~ spl3_14
    | ~ spl3_10
    | spl3_11 ),
    inference(avatar_split_clause,[],[f129,f119,f112,f136])).

fof(f119,plain,
    ( spl3_11
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f129,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_10
    | spl3_11 ),
    inference(subsumption_resolution,[],[f128,f114])).

fof(f128,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_11 ),
    inference(superposition,[],[f121,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f121,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f122,plain,
    ( ~ spl3_11
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f109,f94,f80,f119])).

fof(f109,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f108,f96])).

fof(f108,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f30,f82])).

fof(f30,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(f115,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f107,f99,f94,f80,f112])).

fof(f99,plain,
    ( spl3_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f104,f96])).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f101,f82])).

fof(f101,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f102,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f99])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f97,plain,
    ( spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f73,f65,f94])).

fof(f65,plain,
    ( spl3_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f73,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f67,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f67,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f92,plain,
    ( spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f26,f89,f85])).

fof(f26,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f72,f60,f80])).

fof(f60,plain,
    ( spl3_2
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f72,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f62,f37])).

fof(f62,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f78,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f75])).

fof(f28,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f32,f65])).

fof(f32,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:49:18 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (10048)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (10044)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (10044)Refutation not found, incomplete strategy% (10044)------------------------------
% 0.20/0.48  % (10044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (10044)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (10044)Memory used [KB]: 6012
% 0.20/0.48  % (10044)Time elapsed: 0.002 s
% 0.20/0.48  % (10044)------------------------------
% 0.20/0.48  % (10044)------------------------------
% 0.20/0.48  % (10035)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (10035)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (10043)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  % (10040)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  fof(f458,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f58,f63,f68,f78,f83,f92,f97,f102,f115,f122,f139,f146,f170,f193,f217,f233,f287,f358,f367,f457])).
% 0.20/0.49  fof(f457,plain,(
% 0.20/0.49    ~spl3_6 | spl3_15 | ~spl3_34),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f456])).
% 0.20/0.49  fof(f456,plain,(
% 0.20/0.49    $false | (~spl3_6 | spl3_15 | ~spl3_34)),
% 0.20/0.49    inference(subsumption_resolution,[],[f455,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.49  fof(f455,plain,(
% 0.20/0.49    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl3_6 | spl3_15 | ~spl3_34)),
% 0.20/0.49    inference(forward_demodulation,[],[f278,f329])).
% 0.20/0.49  fof(f329,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | ~spl3_34),
% 0.20/0.49    inference(avatar_component_clause,[],[f327])).
% 0.20/0.49  fof(f327,plain,(
% 0.20/0.49    spl3_34 <=> k1_xboole_0 = sK2),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.49  fof(f278,plain,(
% 0.20/0.49    k1_xboole_0 != k1_relat_1(sK2) | (~spl3_6 | spl3_15)),
% 0.20/0.49    inference(superposition,[],[f145,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl3_6 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k1_relat_1(sK2) | spl3_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f143])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    spl3_15 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.49  fof(f367,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2)) | k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2)) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f358,plain,(
% 0.20/0.49    spl3_34 | ~spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f357,f166,f327])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    spl3_18 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.49  fof(f357,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | ~spl3_18),
% 0.20/0.49    inference(forward_demodulation,[],[f356,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.20/0.49  fof(f356,plain,(
% 0.20/0.49    sK2 = k9_relat_1(k1_xboole_0,sK2) | ~spl3_18),
% 0.20/0.49    inference(forward_demodulation,[],[f355,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.49  fof(f355,plain,(
% 0.20/0.49    sK2 = k9_relat_1(k6_relat_1(k1_xboole_0),sK2) | ~spl3_18),
% 0.20/0.49    inference(resolution,[],[f167,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f166])).
% 0.20/0.49  fof(f287,plain,(
% 0.20/0.49    ~spl3_6 | ~spl3_10 | spl3_18),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f286])).
% 0.20/0.49  fof(f286,plain,(
% 0.20/0.49    $false | (~spl3_6 | ~spl3_10 | spl3_18)),
% 0.20/0.49    inference(subsumption_resolution,[],[f285,f168])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl3_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f166])).
% 0.20/0.49  fof(f285,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_6 | ~spl3_10)),
% 0.20/0.49    inference(forward_demodulation,[],[f272,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f272,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | (~spl3_6 | ~spl3_10)),
% 0.20/0.49    inference(superposition,[],[f114,f87])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f112])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    spl3_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    spl3_25 | ~spl3_1 | ~spl3_4 | ~spl3_5 | spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f226,f190,f112,f94,f89,f80,f75,f55,f230])).
% 0.20/0.49  fof(f230,plain,(
% 0.20/0.49    spl3_25 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    spl3_1 <=> v1_funct_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    spl3_4 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl3_5 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl3_7 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    spl3_8 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    spl3_19 <=> k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2)) | (~spl3_1 | ~spl3_4 | ~spl3_5 | spl3_7 | ~spl3_8 | ~spl3_10 | ~spl3_19)),
% 0.20/0.49    inference(forward_demodulation,[],[f180,f192])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2) | ~spl3_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f190])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k9_relat_1(sK2,k2_struct_0(sK0))) | (~spl3_1 | ~spl3_4 | ~spl3_5 | spl3_7 | ~spl3_8 | ~spl3_10)),
% 0.20/0.49    inference(forward_demodulation,[],[f179,f116])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X0] : (k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl3_10),
% 0.20/0.49    inference(resolution,[],[f114,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0))) | (~spl3_1 | ~spl3_4 | ~spl3_5 | spl3_7 | ~spl3_8 | ~spl3_10)),
% 0.20/0.49    inference(forward_demodulation,[],[f178,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f80])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK0))) | (~spl3_1 | ~spl3_4 | ~spl3_5 | spl3_7 | ~spl3_8 | ~spl3_10)),
% 0.20/0.49    inference(forward_demodulation,[],[f177,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f94])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))) | (~spl3_1 | ~spl3_4 | ~spl3_5 | spl3_7 | ~spl3_8 | ~spl3_10)),
% 0.20/0.49    inference(subsumption_resolution,[],[f176,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    k1_xboole_0 != k2_struct_0(sK1) | spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f89])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    k1_xboole_0 = k2_struct_0(sK1) | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))) | (~spl3_1 | ~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_10)),
% 0.20/0.49    inference(forward_demodulation,[],[f175,f82])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))) | (~spl3_1 | ~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_10)),
% 0.20/0.49    inference(subsumption_resolution,[],[f174,f114])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))) | (~spl3_1 | ~spl3_4 | ~spl3_5 | ~spl3_8)),
% 0.20/0.49    inference(forward_demodulation,[],[f173,f96])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))) | (~spl3_1 | ~spl3_4 | ~spl3_5)),
% 0.20/0.49    inference(forward_demodulation,[],[f171,f82])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))) | (~spl3_1 | ~spl3_4)),
% 0.20/0.49    inference(resolution,[],[f69,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f75])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,sK2,k7_relset_1(X0,X1,sK2,X0)) = X0) ) | ~spl3_1),
% 0.20/0.49    inference(resolution,[],[f57,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    v1_funct_1(sK2) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f55])).
% 0.20/0.49  fof(f217,plain,(
% 0.20/0.49    spl3_23 | ~spl3_10 | ~spl3_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f210,f190,f112,f214])).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    spl3_23 <=> k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2)) | (~spl3_10 | ~spl3_19)),
% 0.20/0.49    inference(forward_demodulation,[],[f154,f192])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k9_relat_1(sK2,k2_struct_0(sK0))) | ~spl3_10),
% 0.20/0.49    inference(subsumption_resolution,[],[f149,f114])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k9_relat_1(sK2,k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_10),
% 0.20/0.49    inference(superposition,[],[f47,f116])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    spl3_19 | ~spl3_10 | ~spl3_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f186,f158,f112,f190])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    spl3_16 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k9_relat_1(sK2,k2_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2) | (~spl3_10 | ~spl3_16)),
% 0.20/0.49    inference(subsumption_resolution,[],[f184,f114])).
% 0.20/0.49  fof(f184,plain,(
% 0.20/0.49    k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_16),
% 0.20/0.49    inference(superposition,[],[f160,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k9_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f158])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    spl3_16 | ~spl3_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f155,f112,f158])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k9_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_10),
% 0.20/0.49    inference(subsumption_resolution,[],[f150,f114])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k9_relat_1(sK2,k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_10),
% 0.20/0.49    inference(superposition,[],[f44,f116])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ~spl3_15 | ~spl3_10 | spl3_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f141,f136,f112,f143])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    spl3_14 <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k1_relat_1(sK2) | (~spl3_10 | spl3_14)),
% 0.20/0.49    inference(subsumption_resolution,[],[f140,f114])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_14),
% 0.20/0.49    inference(superposition,[],[f138,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | spl3_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f136])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ~spl3_14 | ~spl3_10 | spl3_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f129,f119,f112,f136])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    spl3_11 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_10 | spl3_11)),
% 0.20/0.49    inference(subsumption_resolution,[],[f128,f114])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_11),
% 0.20/0.49    inference(superposition,[],[f121,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f119])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ~spl3_11 | ~spl3_5 | ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f109,f94,f80,f119])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl3_5 | ~spl3_8)),
% 0.20/0.49    inference(forward_demodulation,[],[f108,f96])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | ~spl3_5),
% 0.20/0.49    inference(forward_demodulation,[],[f30,f82])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f13])).
% 0.20/0.49  fof(f13,conjecture,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl3_10 | ~spl3_5 | ~spl3_8 | ~spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f107,f99,f94,f80,f112])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    spl3_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_8 | ~spl3_9)),
% 0.20/0.49    inference(forward_demodulation,[],[f104,f96])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_9)),
% 0.20/0.49    inference(forward_demodulation,[],[f101,f82])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f99])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f29,f99])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    spl3_8 | ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f73,f65,f94])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl3_3 <=> l1_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_3),
% 0.20/0.49    inference(resolution,[],[f67,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    l1_struct_0(sK0) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f65])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl3_6 | ~spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f89,f85])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl3_5 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f72,f60,f80])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    spl3_2 <=> l1_struct_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_2),
% 0.20/0.49    inference(resolution,[],[f62,f37])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    l1_struct_0(sK1) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f60])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f28,f75])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f65])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    l1_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f60])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    l1_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f27,f55])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (10035)------------------------------
% 0.20/0.49  % (10035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (10035)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (10035)Memory used [KB]: 10874
% 0.20/0.49  % (10035)Time elapsed: 0.077 s
% 0.20/0.49  % (10035)------------------------------
% 0.20/0.49  % (10035)------------------------------
% 0.20/0.49  % (10031)Success in time 0.125 s
%------------------------------------------------------------------------------
