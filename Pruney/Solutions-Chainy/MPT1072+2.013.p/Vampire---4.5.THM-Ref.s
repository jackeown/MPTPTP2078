%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 237 expanded)
%              Number of leaves         :   25 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  396 (1048 expanded)
%              Number of equality atoms :   36 (  43 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f72,f77,f89,f108,f117,f127,f134,f143,f176,f229])).

fof(f229,plain,
    ( ~ spl4_15
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f186,f78])).

fof(f78,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f33,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f186,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k1_xboole_0)
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f140,f170])).

fof(f170,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl4_18
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f140,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_15
  <=> r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f176,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | spl4_13 ),
    inference(avatar_split_clause,[],[f175,f124,f84,f59,f54,f49,f168])).

fof(f49,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f54,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f59,plain,
    ( spl4_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f84,plain,
    ( spl4_8
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f124,plain,
    ( spl4_13
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f175,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | spl4_13 ),
    inference(subsumption_resolution,[],[f174,f61])).

fof(f61,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f174,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_13 ),
    inference(subsumption_resolution,[],[f173,f56])).

fof(f56,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f173,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_8
    | spl4_13 ),
    inference(subsumption_resolution,[],[f172,f51])).

fof(f51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f172,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | ~ spl4_8
    | spl4_13 ),
    inference(subsumption_resolution,[],[f166,f86])).

fof(f86,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f166,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK2,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | spl4_13 ),
    inference(resolution,[],[f40,f126])).

fof(f126,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f124])).

% (16203)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f143,plain,
    ( spl4_15
    | spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f142,f131,f69,f138])).

fof(f69,plain,
    ( spl4_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f131,plain,
    ( spl4_14
  <=> m1_subset_1(k1_funct_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f142,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | spl4_6
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f136,f71])).

fof(f71,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f136,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | ~ spl4_14 ),
    inference(resolution,[],[f133,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f133,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK2),sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f134,plain,
    ( spl4_14
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f128,f114,f105,f131])).

fof(f105,plain,
    ( spl4_11
  <=> m1_subset_1(k3_funct_2(sK0,sK1,sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f114,plain,
    ( spl4_12
  <=> k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f128,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK2),sK1)
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f107,f116])).

fof(f116,plain,
    ( k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f107,plain,
    ( m1_subset_1(k3_funct_2(sK0,sK1,sK3,sK2),sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f127,plain,
    ( ~ spl4_13
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(avatar_split_clause,[],[f122,f74,f64,f59,f54,f49,f44,f124])).

fof(f44,plain,
    ( spl4_1
  <=> r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f64,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f74,plain,
    ( spl4_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f122,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(subsumption_resolution,[],[f121,f76])).

fof(f76,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f121,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | v1_xboole_0(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f120,f61])).

fof(f120,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f119,f56])).

fof(f119,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f118,f51])).

fof(f118,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | spl4_1
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f110,f66])).

fof(f66,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f110,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | spl4_1 ),
    inference(superposition,[],[f46,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f46,plain,
    ( ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f117,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(avatar_split_clause,[],[f109,f74,f64,f59,f54,f49,f114])).

fof(f109,plain,
    ( k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f76,f61,f66,f56,f51,f39])).

fof(f108,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(avatar_split_clause,[],[f102,f74,f64,f59,f54,f49,f105])).

fof(f102,plain,
    ( m1_subset_1(k3_funct_2(sK0,sK1,sK3,sK2),sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f76,f61,f66,f56,f51,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f89,plain,
    ( spl4_8
    | ~ spl4_5
    | spl4_7 ),
    inference(avatar_split_clause,[],[f88,f74,f64,f84])).

fof(f88,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_5
    | spl4_7 ),
    inference(subsumption_resolution,[],[f81,f76])).

fof(f81,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK2,sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f34,f66])).

fof(f77,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f26,f74])).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,sK0)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f22,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,X0) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(sK0,X1,X3,X2),k2_relset_1(sK0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
                  & v1_funct_2(X3,sK0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,sK0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k3_funct_2(sK0,X1,X3,X2),k2_relset_1(sK0,X1,X3))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
                & v1_funct_2(X3,sK0,X1)
                & v1_funct_1(X3) )
            & m1_subset_1(X2,sK0) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k3_funct_2(sK0,sK1,X3,X2),k2_relset_1(sK0,sK1,X3))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
              & v1_funct_2(X3,sK0,sK1)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,sK0) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(k3_funct_2(sK0,sK1,X3,X2),k2_relset_1(sK0,sK1,X3))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
            & v1_funct_2(X3,sK0,sK1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,sK0) )
   => ( ? [X3] :
          ( ~ r2_hidden(k3_funct_2(sK0,sK1,X3,sK2),k2_relset_1(sK0,sK1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ~ r2_hidden(k3_funct_2(sK0,sK1,X3,sK2),k2_relset_1(sK0,sK1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

fof(f72,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f31,f49])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f32,f44])).

fof(f32,plain,(
    ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (16212)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.45  % (16212)Refutation not found, incomplete strategy% (16212)------------------------------
% 0.20/0.45  % (16212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (16212)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (16212)Memory used [KB]: 6140
% 0.20/0.45  % (16212)Time elapsed: 0.037 s
% 0.20/0.45  % (16212)------------------------------
% 0.20/0.45  % (16212)------------------------------
% 0.20/0.47  % (16216)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (16220)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (16220)Refutation not found, incomplete strategy% (16220)------------------------------
% 0.20/0.47  % (16220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16220)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (16220)Memory used [KB]: 10490
% 0.20/0.47  % (16220)Time elapsed: 0.063 s
% 0.20/0.47  % (16220)------------------------------
% 0.20/0.47  % (16220)------------------------------
% 0.20/0.47  % (16201)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (16201)Refutation not found, incomplete strategy% (16201)------------------------------
% 0.20/0.47  % (16201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16201)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (16201)Memory used [KB]: 10618
% 0.20/0.47  % (16201)Time elapsed: 0.063 s
% 0.20/0.47  % (16201)------------------------------
% 0.20/0.47  % (16201)------------------------------
% 0.20/0.48  % (16208)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (16211)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (16207)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (16204)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (16216)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f72,f77,f89,f108,f117,f127,f134,f143,f176,f229])).
% 0.20/0.48  fof(f229,plain,(
% 0.20/0.48    ~spl4_15 | ~spl4_18),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f228])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    $false | (~spl4_15 | ~spl4_18)),
% 0.20/0.48    inference(subsumption_resolution,[],[f186,f78])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(superposition,[],[f33,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK3,sK2),k1_xboole_0) | (~spl4_15 | ~spl4_18)),
% 0.20/0.49    inference(backward_demodulation,[],[f140,f170])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~spl4_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f168])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    spl4_18 <=> k1_xboole_0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK3,sK2),sK1) | ~spl4_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f138])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    spl4_15 <=> r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    spl4_18 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_8 | spl4_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f175,f124,f84,f59,f54,f49,f168])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl4_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    spl4_4 <=> v1_funct_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl4_8 <=> r2_hidden(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    spl4_13 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_8 | spl4_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f174,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    v1_funct_1(sK3) | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f59])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~v1_funct_1(sK3) | (~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f173,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    v1_funct_2(sK3,sK0,sK1) | ~spl4_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f54])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | (~spl4_2 | ~spl4_8 | spl4_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f172,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f49])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | (~spl4_8 | spl4_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f166,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    r2_hidden(sK2,sK0) | ~spl4_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f84])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~r2_hidden(sK2,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | spl4_13),
% 0.20/0.49    inference(resolution,[],[f40,f126])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | spl4_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f124])).
% 0.20/0.49  % (16203)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    spl4_15 | spl4_6 | ~spl4_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f142,f131,f69,f138])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl4_6 <=> v1_xboole_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    spl4_14 <=> m1_subset_1(k1_funct_1(sK3,sK2),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK3,sK2),sK1) | (spl4_6 | ~spl4_14)),
% 0.20/0.49    inference(subsumption_resolution,[],[f136,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1) | spl4_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f69])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    v1_xboole_0(sK1) | r2_hidden(k1_funct_1(sK3,sK2),sK1) | ~spl4_14),
% 0.20/0.49    inference(resolution,[],[f133,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    m1_subset_1(k1_funct_1(sK3,sK2),sK1) | ~spl4_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f131])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    spl4_14 | ~spl4_11 | ~spl4_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f128,f114,f105,f131])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl4_11 <=> m1_subset_1(k3_funct_2(sK0,sK1,sK3,sK2),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl4_12 <=> k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    m1_subset_1(k1_funct_1(sK3,sK2),sK1) | (~spl4_11 | ~spl4_12)),
% 0.20/0.49    inference(backward_demodulation,[],[f107,f116])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2) | ~spl4_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f114])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    m1_subset_1(k3_funct_2(sK0,sK1,sK3,sK2),sK1) | ~spl4_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f105])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    ~spl4_13 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f122,f74,f64,f59,f54,f49,f44,f124])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    spl4_1 <=> r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    spl4_5 <=> m1_subset_1(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl4_7 <=> v1_xboole_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f121,f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ~v1_xboole_0(sK0) | spl4_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f74])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | v1_xboole_0(sK0) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f120,f61])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f119,f56])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | (spl4_1 | ~spl4_2 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f118,f51])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | (spl4_1 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f110,f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    m1_subset_1(sK2,sK0) | ~spl4_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f64])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | spl4_1),
% 0.20/0.49    inference(superposition,[],[f46,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f44])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl4_12 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f109,f74,f64,f59,f54,f49,f114])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    k3_funct_2(sK0,sK1,sK3,sK2) = k1_funct_1(sK3,sK2) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f76,f61,f66,f56,f51,f39])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    spl4_11 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f102,f74,f64,f59,f54,f49,f105])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    m1_subset_1(k3_funct_2(sK0,sK1,sK3,sK2),sK1) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f76,f61,f66,f56,f51,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl4_8 | ~spl4_5 | spl4_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f88,f74,f64,f84])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    r2_hidden(sK2,sK0) | (~spl4_5 | spl4_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f81,f76])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    v1_xboole_0(sK0) | r2_hidden(sK2,sK0) | ~spl4_5),
% 0.20/0.49    inference(resolution,[],[f34,f66])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ~spl4_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f74])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ~v1_xboole_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    (((~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,sK0)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f22,f21,f20,f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(sK0,X1,X3,X2),k2_relset_1(sK0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X3,sK0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,sK0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(sK0,X1,X3,X2),k2_relset_1(sK0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X3,sK0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,sK0)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(sK0,sK1,X3,X2),k2_relset_1(sK0,sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(X2,sK0)) & ~v1_xboole_0(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(sK0,sK1,X3,X2),k2_relset_1(sK0,sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(X2,sK0)) => (? [X3] : (~r2_hidden(k3_funct_2(sK0,sK1,X3,sK2),k2_relset_1(sK0,sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X3] : (~r2_hidden(k3_funct_2(sK0,sK1,X3,sK2),k2_relset_1(sK0,sK1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f7])).
% 0.20/0.49  fof(f7,conjecture,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ~spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f27,f69])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    spl4_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f28,f64])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    m1_subset_1(sK2,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f29,f59])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    v1_funct_1(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    spl4_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f54])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f49])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ~spl4_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f44])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ~r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (16216)------------------------------
% 0.20/0.49  % (16216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16216)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (16216)Memory used [KB]: 10746
% 0.20/0.49  % (16216)Time elapsed: 0.068 s
% 0.20/0.49  % (16216)------------------------------
% 0.20/0.49  % (16216)------------------------------
% 0.20/0.49  % (16210)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (16214)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (16199)Success in time 0.138 s
%------------------------------------------------------------------------------
