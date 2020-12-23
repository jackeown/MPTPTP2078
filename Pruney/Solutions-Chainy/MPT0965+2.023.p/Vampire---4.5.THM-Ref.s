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
% DateTime   : Thu Dec  3 13:00:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 185 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  326 ( 540 expanded)
%              Number of equality atoms :   42 (  70 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f73,f84,f88,f92,f106,f110,f116,f127,f134,f145,f150,f172,f198,f209,f213])).

fof(f213,plain,
    ( spl5_6
    | spl5_25
    | ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl5_6
    | spl5_25
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f211,f87])).

fof(f87,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_6
  <=> r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f211,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | spl5_25
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f210,f197])).

fof(f197,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_25 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl5_25
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f210,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | ~ spl5_26 ),
    inference(resolution,[],[f208,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f208,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK2),sK1)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl5_26
  <=> m1_subset_1(k1_funct_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f209,plain,
    ( spl5_26
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f202,f170,f125,f207])).

fof(f125,plain,
    ( spl5_12
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f170,plain,
    ( spl5_20
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f202,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK2),sK1)
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(resolution,[],[f174,f126])).

fof(f126,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X0))
        | m1_subset_1(k1_funct_1(sK3,sK2),X0) )
    | ~ spl5_20 ),
    inference(resolution,[],[f171,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f171,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f170])).

fof(f198,plain,
    ( ~ spl5_25
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f187,f170,f125,f196])).

fof(f187,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(resolution,[],[f175,f126])).

fof(f175,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl5_20 ),
    inference(resolution,[],[f171,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f172,plain,
    ( spl5_20
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f167,f147,f104,f67,f63,f170])).

fof(f63,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f67,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f104,plain,
    ( spl5_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f147,plain,
    ( spl5_17
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f167,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_17 ),
    inference(resolution,[],[f153,f68])).

fof(f68,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) )
    | ~ spl5_1
    | ~ spl5_8
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f152,f105])).

fof(f105,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK3)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) )
    | ~ spl5_1
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f151,f64])).

fof(f64,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) )
    | ~ spl5_17 ),
    inference(superposition,[],[f37,f148])).

fof(f148,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f147])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f150,plain,
    ( spl5_17
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f149,f143,f132,f147])).

fof(f132,plain,
    ( spl5_13
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f143,plain,
    ( spl5_16
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f149,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f144,f133])).

fof(f133,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f132])).

fof(f144,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( spl5_16
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f94,f90,f143])).

fof(f90,plain,
    ( spl5_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f94,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl5_7 ),
    inference(resolution,[],[f91,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f91,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f134,plain,
    ( spl5_13
    | spl5_3
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f101,f90,f82,f71,f132])).

fof(f71,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f82,plain,
    ( spl5_5
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f101,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl5_3
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f100,f83])).

fof(f83,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f100,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl5_3
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f96,f72])).

fof(f72,plain,
    ( k1_xboole_0 != sK1
    | spl5_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f96,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f91,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f127,plain,
    ( spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f122,f114,f125])).

fof(f114,plain,
    ( spl5_10
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f122,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl5_10 ),
    inference(resolution,[],[f115,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f115,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl5_10
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f112,f108,f104,f114])).

fof(f108,plain,
    ( spl5_9
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f112,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f111,f105])).

fof(f111,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl5_9 ),
    inference(resolution,[],[f109,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f109,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,
    ( spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f93,f90,f108])).

fof(f93,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f91,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f106,plain,
    ( spl5_8
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f102,f90,f104])).

fof(f102,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f98,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f98,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl5_7 ),
    inference(resolution,[],[f91,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f92,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f33,f90])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f88,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f36,f86])).

fof(f36,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f17])).

% (18940)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f84,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f35,f71])).

fof(f35,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f34,f67])).

fof(f34,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 10:05:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (18924)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (18924)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (18939)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (18931)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f65,f69,f73,f84,f88,f92,f106,f110,f116,f127,f134,f145,f150,f172,f198,f209,f213])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    spl5_6 | spl5_25 | ~spl5_26),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f212])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    $false | (spl5_6 | spl5_25 | ~spl5_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f211,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK3,sK2),sK1) | spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl5_6 <=> r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK3,sK2),sK1) | (spl5_25 | ~spl5_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f210,f197])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | spl5_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f196])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    spl5_25 <=> v1_xboole_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | r2_hidden(k1_funct_1(sK3,sK2),sK1) | ~spl5_26),
% 0.21/0.48    inference(resolution,[],[f208,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    m1_subset_1(k1_funct_1(sK3,sK2),sK1) | ~spl5_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f207])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    spl5_26 <=> m1_subset_1(k1_funct_1(sK3,sK2),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    spl5_26 | ~spl5_12 | ~spl5_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f202,f170,f125,f207])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    spl5_12 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    spl5_20 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    m1_subset_1(k1_funct_1(sK3,sK2),sK1) | (~spl5_12 | ~spl5_20)),
% 0.21/0.48    inference(resolution,[],[f174,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl5_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f125])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X0)) | m1_subset_1(k1_funct_1(sK3,sK2),X0)) ) | ~spl5_20),
% 0.21/0.48    inference(resolution,[],[f171,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | ~spl5_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f170])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ~spl5_25 | ~spl5_12 | ~spl5_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f187,f170,f125,f196])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | (~spl5_12 | ~spl5_20)),
% 0.21/0.48    inference(resolution,[],[f175,f126])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X1)) | ~v1_xboole_0(X1)) ) | ~spl5_20),
% 0.21/0.48    inference(resolution,[],[f171,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl5_20 | ~spl5_1 | ~spl5_2 | ~spl5_8 | ~spl5_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f167,f147,f104,f67,f63,f170])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl5_1 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl5_2 <=> r2_hidden(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl5_8 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    spl5_17 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | (~spl5_1 | ~spl5_2 | ~spl5_8 | ~spl5_17)),
% 0.21/0.48    inference(resolution,[],[f153,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    r2_hidden(sK2,sK0) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) ) | (~spl5_1 | ~spl5_8 | ~spl5_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f152,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl5_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK3) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) ) | (~spl5_1 | ~spl5_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f151,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) ) | ~spl5_17),
% 0.21/0.48    inference(superposition,[],[f37,f148])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK3) | ~spl5_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f147])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    spl5_17 | ~spl5_13 | ~spl5_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f149,f143,f132,f147])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl5_13 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl5_16 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK3) | (~spl5_13 | ~spl5_16)),
% 0.21/0.48    inference(forward_demodulation,[],[f144,f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f132])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl5_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f143])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    spl5_16 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f94,f90,f143])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl5_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl5_7),
% 0.21/0.48    inference(resolution,[],[f91,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f90])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl5_13 | spl5_3 | ~spl5_5 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f101,f90,f82,f71,f132])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl5_3 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl5_5 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK3) | (spl5_3 | ~spl5_5 | ~spl5_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f100,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f82])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl5_3 | ~spl5_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl5_7),
% 0.21/0.48    inference(resolution,[],[f91,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    spl5_12 | ~spl5_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f122,f114,f125])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl5_10 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl5_10),
% 0.21/0.48    inference(resolution,[],[f115,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    r1_tarski(k2_relat_1(sK3),sK1) | ~spl5_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f114])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl5_10 | ~spl5_8 | ~spl5_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f112,f108,f104,f114])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl5_9 <=> v5_relat_1(sK3,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    r1_tarski(k2_relat_1(sK3),sK1) | (~spl5_8 | ~spl5_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f105])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl5_9),
% 0.21/0.48    inference(resolution,[],[f109,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    v5_relat_1(sK3,sK1) | ~spl5_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f108])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl5_9 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f93,f90,f108])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    v5_relat_1(sK3,sK1) | ~spl5_7),
% 0.21/0.48    inference(resolution,[],[f91,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl5_8 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f102,f90,f104])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl5_7),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl5_7),
% 0.21/0.48    inference(resolution,[],[f91,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f90])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f13])).
% 0.21/0.48  fof(f13,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ~spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f86])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  % (18940)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f82])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ~spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f71])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f67])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    r2_hidden(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f63])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (18924)------------------------------
% 0.21/0.48  % (18924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18924)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (18924)Memory used [KB]: 6268
% 0.21/0.48  % (18924)Time elapsed: 0.069 s
% 0.21/0.48  % (18924)------------------------------
% 0.21/0.48  % (18924)------------------------------
% 0.21/0.48  % (18923)Success in time 0.119 s
%------------------------------------------------------------------------------
