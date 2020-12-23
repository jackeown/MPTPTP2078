%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 146 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :  298 ( 479 expanded)
%              Number of equality atoms :   47 (  72 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f73,f78,f83,f101,f106,f111,f127,f136,f140,f150,f155,f158])).

fof(f158,plain,
    ( ~ spl6_2
    | spl6_5
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl6_2
    | spl6_5
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f156,f61])).

fof(f61,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f156,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl6_5
    | ~ spl6_17 ),
    inference(resolution,[],[f149,f77])).

fof(f77,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_5
  <=> r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f149,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl6_17
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f155,plain,
    ( spl6_3
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl6_3
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f153,f66])).

fof(f66,plain,
    ( k1_xboole_0 != sK1
    | spl6_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f153,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_16 ),
    inference(resolution,[],[f151,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f151,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl6_16 ),
    inference(resolution,[],[f146,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f146,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_16
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f150,plain,
    ( spl6_16
    | spl6_17
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f142,f134,f98,f148,f144])).

fof(f98,plain,
    ( spl6_8
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f134,plain,
    ( spl6_15
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,sK0)
        | m1_subset_1(k1_funct_1(sK3,X1),X0)
        | ~ v5_relat_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | v1_xboole_0(sK1)
        | r2_hidden(k1_funct_1(sK3,X0),sK1) )
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(resolution,[],[f141,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

% (24980)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f141,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_funct_1(sK3,X0),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(resolution,[],[f135,f100])).

fof(f100,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK3,X0)
        | m1_subset_1(k1_funct_1(sK3,X1),X0)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f140,plain,
    ( ~ spl6_6
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl6_6
    | spl6_14 ),
    inference(subsumption_resolution,[],[f138,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f138,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_6
    | spl6_14 ),
    inference(resolution,[],[f137,f82])).

fof(f82,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_14 ),
    inference(resolution,[],[f132,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f132,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f136,plain,
    ( ~ spl6_14
    | spl6_15
    | ~ spl6_1
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f128,f113,f54,f134,f130])).

fof(f54,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f113,plain,
    ( spl6_11
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ v5_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3)
        | m1_subset_1(k1_funct_1(sK3,X1),X0) )
    | ~ spl6_1
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f68,f115])).

fof(f115,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(X1,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X1),X0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f56,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | m1_subset_1(k1_funct_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(f56,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f127,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | sK0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f111,plain,
    ( spl6_10
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f91,f80,f70,f64,f108])).

fof(f108,plain,
    ( spl6_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f70,plain,
    ( spl6_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f91,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f90,f72])).

fof(f72,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f90,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f85,f66])).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f82,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f106,plain,
    ( spl6_9
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f88,f80,f103])).

fof(f103,plain,
    ( spl6_9
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f88,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_6 ),
    inference(resolution,[],[f82,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f101,plain,
    ( spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f87,f80,f98])).

fof(f87,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f82,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f83,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f27,f80])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f78,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f26,f70])).

fof(f26,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:07:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (24981)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (24976)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (24974)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (24988)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (24977)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (24974)Refutation not found, incomplete strategy% (24974)------------------------------
% 0.22/0.50  % (24974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24974)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (24974)Memory used [KB]: 10618
% 0.22/0.50  % (24974)Time elapsed: 0.081 s
% 0.22/0.50  % (24974)------------------------------
% 0.22/0.50  % (24974)------------------------------
% 0.22/0.50  % (24985)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (24973)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (24985)Refutation not found, incomplete strategy% (24985)------------------------------
% 0.22/0.50  % (24985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24985)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (24985)Memory used [KB]: 6140
% 0.22/0.50  % (24985)Time elapsed: 0.085 s
% 0.22/0.50  % (24985)------------------------------
% 0.22/0.50  % (24985)------------------------------
% 0.22/0.50  % (24973)Refutation not found, incomplete strategy% (24973)------------------------------
% 0.22/0.50  % (24973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24973)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (24973)Memory used [KB]: 6140
% 0.22/0.50  % (24973)Time elapsed: 0.058 s
% 0.22/0.50  % (24973)------------------------------
% 0.22/0.50  % (24973)------------------------------
% 0.22/0.50  % (24982)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (24978)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (24976)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f57,f62,f67,f73,f78,f83,f101,f106,f111,f127,f136,f140,f150,f155,f158])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    ~spl6_2 | spl6_5 | ~spl6_17),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f157])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    $false | (~spl6_2 | spl6_5 | ~spl6_17)),
% 0.22/0.50    inference(subsumption_resolution,[],[f156,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    r2_hidden(sK2,sK0) | ~spl6_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl6_2 <=> r2_hidden(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    ~r2_hidden(sK2,sK0) | (spl6_5 | ~spl6_17)),
% 0.22/0.50    inference(resolution,[],[f149,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ~r2_hidden(k1_funct_1(sK3,sK2),sK1) | spl6_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl6_5 <=> r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK1) | ~r2_hidden(X0,sK0)) ) | ~spl6_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f148])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    spl6_17 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    spl6_3 | ~spl6_16),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f154])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    $false | (spl6_3 | ~spl6_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f153,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    k1_xboole_0 != sK1 | spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl6_3 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~spl6_16),
% 0.22/0.50    inference(resolution,[],[f151,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl6_16),
% 0.22/0.50    inference(resolution,[],[f146,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    v1_xboole_0(sK1) | ~spl6_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f144])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    spl6_16 <=> v1_xboole_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    spl6_16 | spl6_17 | ~spl6_8 | ~spl6_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f142,f134,f98,f148,f144])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    spl6_8 <=> v5_relat_1(sK3,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    spl6_15 <=> ! [X1,X0] : (~r2_hidden(X1,sK0) | m1_subset_1(k1_funct_1(sK3,X1),X0) | ~v5_relat_1(sK3,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK0) | v1_xboole_0(sK1) | r2_hidden(k1_funct_1(sK3,X0),sK1)) ) | (~spl6_8 | ~spl6_15)),
% 0.22/0.50    inference(resolution,[],[f141,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  % (24980)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k1_funct_1(sK3,X0),sK1) | ~r2_hidden(X0,sK0)) ) | (~spl6_8 | ~spl6_15)),
% 0.22/0.50    inference(resolution,[],[f135,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    v5_relat_1(sK3,sK1) | ~spl6_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f98])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v5_relat_1(sK3,X0) | m1_subset_1(k1_funct_1(sK3,X1),X0) | ~r2_hidden(X1,sK0)) ) | ~spl6_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f134])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    ~spl6_6 | spl6_14),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f139])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    $false | (~spl6_6 | spl6_14)),
% 0.22/0.50    inference(subsumption_resolution,[],[f138,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl6_6 | spl6_14)),
% 0.22/0.50    inference(resolution,[],[f137,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_14),
% 0.22/0.50    inference(resolution,[],[f132,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ~v1_relat_1(sK3) | spl6_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f130])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    spl6_14 <=> v1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    ~spl6_14 | spl6_15 | ~spl6_1 | ~spl6_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f128,f113,f54,f134,f130])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    spl6_1 <=> v1_funct_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl6_11 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | ~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3) | m1_subset_1(k1_funct_1(sK3,X1),X0)) ) | (~spl6_1 | ~spl6_11)),
% 0.22/0.50    inference(forward_demodulation,[],[f68,f115])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK3) | ~spl6_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f113])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3) | ~r2_hidden(X1,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X1),X0)) ) | ~spl6_1),
% 0.22/0.50    inference(resolution,[],[f56,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | m1_subset_1(k1_funct_1(X2,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    v1_funct_1(sK3) | ~spl6_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f54])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    sK0 != k1_relset_1(sK0,sK1,sK3) | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) | sK0 = k1_relat_1(sK3)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl6_10 | spl6_3 | ~spl6_4 | ~spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f91,f80,f70,f64,f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl6_10 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl6_4 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | (spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f90,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,sK1) | ~spl6_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f70])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl6_3 | ~spl6_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f85,f66])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl6_6),
% 0.22/0.50    inference(resolution,[],[f82,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    spl6_9 | ~spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f88,f80,f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl6_9 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl6_6),
% 0.22/0.50    inference(resolution,[],[f82,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl6_8 | ~spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f87,f80,f98])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    v5_relat_1(sK3,sK1) | ~spl6_6),
% 0.22/0.50    inference(resolution,[],[f82,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f80])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ~spl6_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f75])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ~r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f70])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ~spl6_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f64])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    k1_xboole_0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f59])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    r2_hidden(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    spl6_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f25,f54])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (24976)------------------------------
% 0.22/0.50  % (24976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24976)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (24976)Memory used [KB]: 10618
% 0.22/0.50  % (24976)Time elapsed: 0.087 s
% 0.22/0.50  % (24976)------------------------------
% 0.22/0.50  % (24976)------------------------------
% 0.22/0.50  % (24968)Success in time 0.14 s
%------------------------------------------------------------------------------
