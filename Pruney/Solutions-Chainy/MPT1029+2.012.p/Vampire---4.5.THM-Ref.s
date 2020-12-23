%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 208 expanded)
%              Number of leaves         :   33 (  98 expanded)
%              Depth                    :    6
%              Number of atoms          :  342 ( 646 expanded)
%              Number of equality atoms :   36 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f230,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f47,f54,f58,f62,f66,f70,f74,f83,f87,f93,f97,f102,f113,f117,f122,f130,f145,f167,f172,f177,f204,f214,f224,f229])).

fof(f229,plain,
    ( ~ spl4_8
    | spl4_31
    | ~ spl4_35 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl4_8
    | spl4_31
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f226,f203])).

fof(f203,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl4_31 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl4_31
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f226,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_8
    | ~ spl4_35 ),
    inference(superposition,[],[f65,f223])).

fof(f223,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl4_35
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f65,plain,
    ( ! [X0] : v1_partfun1(k6_partfun1(X0),X0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_8
  <=> ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f224,plain,
    ( spl4_35
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f123,f115,f85,f222])).

fof(f85,plain,
    ( spl4_13
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK3(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f115,plain,
    ( spl4_19
  <=> ! [X0] : ~ r2_hidden(X0,k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f123,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(resolution,[],[f116,f86])).

fof(f86,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f116,plain,
    ( ! [X0] : ~ r2_hidden(X0,k6_partfun1(k1_xboole_0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f115])).

fof(f214,plain,
    ( spl4_5
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f149,f143,f68,f52])).

fof(f52,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f143,plain,
    ( spl4_24
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f149,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(resolution,[],[f144,f69])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f144,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f143])).

fof(f204,plain,
    ( ~ spl4_31
    | ~ spl4_13
    | spl4_25
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f186,f175,f165,f85,f202])).

fof(f165,plain,
    ( spl4_25
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f175,plain,
    ( spl4_27
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f186,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_13
    | spl4_25
    | ~ spl4_27 ),
    inference(backward_demodulation,[],[f166,f182])).

% (26024)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f182,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_13
    | ~ spl4_27 ),
    inference(resolution,[],[f176,f86])).

fof(f176,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f175])).

fof(f166,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f165])).

fof(f177,plain,
    ( spl4_27
    | ~ spl4_16
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f173,f170,f100,f175])).

fof(f100,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f170,plain,
    ( spl4_26
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f173,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl4_16
    | ~ spl4_26 ),
    inference(resolution,[],[f171,f101])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f100])).

fof(f171,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f170])).

fof(f172,plain,
    ( spl4_26
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f157,f143,f72,f68,f56,f170])).

fof(f56,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f72,plain,
    ( spl4_10
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f157,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f155,f73])).

fof(f73,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f155,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f57,f149])).

fof(f57,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f167,plain,
    ( ~ spl4_25
    | spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f160,f49,f41,f165])).

fof(f41,plain,
    ( spl4_2
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f49,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f160,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f42,f50])).

fof(f50,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f42,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f145,plain,
    ( spl4_24
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f137,f128,f56,f45,f143])).

fof(f45,plain,
    ( spl4_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f128,plain,
    ( spl4_21
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f137,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f136,f57])).

fof(f136,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(resolution,[],[f129,f46])).

fof(f46,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( spl4_21
    | spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f126,f120,f41,f128])).

fof(f120,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f126,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | spl4_2
    | ~ spl4_20 ),
    inference(resolution,[],[f121,f42])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X0)
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( spl4_20
    | ~ spl4_1
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f118,f111,f37,f120])).

fof(f37,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f111,plain,
    ( spl4_18
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) )
    | ~ spl4_1
    | ~ spl4_18 ),
    inference(resolution,[],[f112,f38])).

fof(f38,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f112,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f111])).

fof(f117,plain,
    ( spl4_19
    | ~ spl4_14
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f109,f100,f91,f115])).

fof(f91,plain,
    ( spl4_14
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f109,plain,
    ( ! [X0] : ~ r2_hidden(X0,k6_partfun1(k1_xboole_0))
    | ~ spl4_14
    | ~ spl4_16 ),
    inference(resolution,[],[f101,f92])).

fof(f92,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f113,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f29,f111])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f102,plain,
    ( spl4_16
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f98,f95,f60,f100])).

fof(f60,plain,
    ( spl4_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f95,plain,
    ( spl4_15
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(resolution,[],[f96,f61])).

fof(f61,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f96,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f33,f95])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f93,plain,
    ( spl4_14
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f88,f81,f72,f91])).

fof(f81,plain,
    ( spl4_12
  <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f88,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(superposition,[],[f82,f73])).

fof(f82,plain,
    ( ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f87,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f28,f85])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f83,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f26,f81])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f74,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f34,f72])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f70,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f27,f68])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f66,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f25,f64])).

fof(f25,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f24,f60])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f58,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) )
         => ( v1_partfun1(X2,X0)
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f54,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f17,f52,f49])).

fof(f17,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f20,f37])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (26020)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (26016)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (26031)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (26016)Refutation not found, incomplete strategy% (26016)------------------------------
% 0.20/0.47  % (26016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (26016)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (26016)Memory used [KB]: 6140
% 0.20/0.47  % (26016)Time elapsed: 0.051 s
% 0.20/0.47  % (26016)------------------------------
% 0.20/0.47  % (26016)------------------------------
% 0.20/0.47  % (26031)Refutation not found, incomplete strategy% (26031)------------------------------
% 0.20/0.47  % (26031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (26031)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (26031)Memory used [KB]: 6140
% 0.20/0.47  % (26031)Time elapsed: 0.005 s
% 0.20/0.47  % (26031)------------------------------
% 0.20/0.47  % (26031)------------------------------
% 0.20/0.47  % (26025)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (26025)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f230,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f39,f43,f47,f54,f58,f62,f66,f70,f74,f83,f87,f93,f97,f102,f113,f117,f122,f130,f145,f167,f172,f177,f204,f214,f224,f229])).
% 0.20/0.47  fof(f229,plain,(
% 0.20/0.47    ~spl4_8 | spl4_31 | ~spl4_35),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f228])).
% 0.20/0.47  fof(f228,plain,(
% 0.20/0.47    $false | (~spl4_8 | spl4_31 | ~spl4_35)),
% 0.20/0.47    inference(subsumption_resolution,[],[f226,f203])).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | spl4_31),
% 0.20/0.47    inference(avatar_component_clause,[],[f202])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    spl4_31 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.20/0.47  fof(f226,plain,(
% 0.20/0.47    v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl4_8 | ~spl4_35)),
% 0.20/0.47    inference(superposition,[],[f65,f223])).
% 0.20/0.47  fof(f223,plain,(
% 0.20/0.47    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl4_35),
% 0.20/0.47    inference(avatar_component_clause,[],[f222])).
% 0.20/0.47  fof(f222,plain,(
% 0.20/0.47    spl4_35 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) ) | ~spl4_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl4_8 <=> ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.47  fof(f224,plain,(
% 0.20/0.47    spl4_35 | ~spl4_13 | ~spl4_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f123,f115,f85,f222])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    spl4_13 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    spl4_19 <=> ! [X0] : ~r2_hidden(X0,k6_partfun1(k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    k1_xboole_0 = k6_partfun1(k1_xboole_0) | (~spl4_13 | ~spl4_19)),
% 0.20/0.47    inference(resolution,[],[f116,f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | ~spl4_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f85])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k6_partfun1(k1_xboole_0))) ) | ~spl4_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f115])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    spl4_5 | ~spl4_9 | ~spl4_24),
% 0.20/0.47    inference(avatar_split_clause,[],[f149,f143,f68,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    spl4_5 <=> k1_xboole_0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl4_9 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    spl4_24 <=> v1_xboole_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | (~spl4_9 | ~spl4_24)),
% 0.20/0.47    inference(resolution,[],[f144,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    v1_xboole_0(sK1) | ~spl4_24),
% 0.20/0.47    inference(avatar_component_clause,[],[f143])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    ~spl4_31 | ~spl4_13 | spl4_25 | ~spl4_27),
% 0.20/0.47    inference(avatar_split_clause,[],[f186,f175,f165,f85,f202])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    spl4_25 <=> v1_partfun1(sK2,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    spl4_27 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl4_13 | spl4_25 | ~spl4_27)),
% 0.20/0.47    inference(backward_demodulation,[],[f166,f182])).
% 0.20/0.47  % (26024)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | (~spl4_13 | ~spl4_27)),
% 0.20/0.47    inference(resolution,[],[f176,f86])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl4_27),
% 0.20/0.48    inference(avatar_component_clause,[],[f175])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    ~v1_partfun1(sK2,k1_xboole_0) | spl4_25),
% 0.20/0.48    inference(avatar_component_clause,[],[f165])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    spl4_27 | ~spl4_16 | ~spl4_26),
% 0.20/0.48    inference(avatar_split_clause,[],[f173,f170,f100,f175])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl4_16 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    spl4_26 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl4_16 | ~spl4_26)),
% 0.20/0.48    inference(resolution,[],[f171,f101])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl4_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f100])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_26),
% 0.20/0.48    inference(avatar_component_clause,[],[f170])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    spl4_26 | ~spl4_6 | ~spl4_9 | ~spl4_10 | ~spl4_24),
% 0.20/0.48    inference(avatar_split_clause,[],[f157,f143,f72,f68,f56,f170])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl4_10 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl4_6 | ~spl4_9 | ~spl4_10 | ~spl4_24)),
% 0.20/0.48    inference(forward_demodulation,[],[f155,f73])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl4_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f72])).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl4_6 | ~spl4_9 | ~spl4_24)),
% 0.20/0.48    inference(backward_demodulation,[],[f57,f149])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f56])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    ~spl4_25 | spl4_2 | ~spl4_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f160,f49,f41,f165])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    spl4_2 <=> v1_partfun1(sK2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    spl4_4 <=> k1_xboole_0 = sK0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    ~v1_partfun1(sK2,k1_xboole_0) | (spl4_2 | ~spl4_4)),
% 0.20/0.48    inference(backward_demodulation,[],[f42,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | ~spl4_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f49])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ~v1_partfun1(sK2,sK0) | spl4_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f41])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    spl4_24 | ~spl4_3 | ~spl4_6 | ~spl4_21),
% 0.20/0.48    inference(avatar_split_clause,[],[f137,f128,f56,f45,f143])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl4_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    spl4_21 <=> ! [X0] : (v1_xboole_0(X0) | ~v1_funct_2(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | (~spl4_3 | ~spl4_6 | ~spl4_21)),
% 0.20/0.48    inference(subsumption_resolution,[],[f136,f57])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_3 | ~spl4_21)),
% 0.20/0.48    inference(resolution,[],[f129,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    v1_funct_2(sK2,sK0,sK1) | ~spl4_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f45])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_funct_2(sK2,sK0,X0) | v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | ~spl4_21),
% 0.20/0.48    inference(avatar_component_clause,[],[f128])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    spl4_21 | spl4_2 | ~spl4_20),
% 0.20/0.48    inference(avatar_split_clause,[],[f126,f120,f41,f128])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    spl4_20 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ( ! [X0] : (v1_xboole_0(X0) | ~v1_funct_2(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | (spl4_2 | ~spl4_20)),
% 0.20/0.48    inference(resolution,[],[f121,f42])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_partfun1(sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f120])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    spl4_20 | ~spl4_1 | ~spl4_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f118,f111,f37,f120])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    spl4_1 <=> v1_funct_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    spl4_18 <=> ! [X1,X0,X2] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0)) ) | (~spl4_1 | ~spl4_18)),
% 0.20/0.48    inference(resolution,[],[f112,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    v1_funct_1(sK2) | ~spl4_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f37])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) ) | ~spl4_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f111])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    spl4_19 | ~spl4_14 | ~spl4_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f109,f100,f91,f115])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    spl4_14 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k6_partfun1(k1_xboole_0))) ) | (~spl4_14 | ~spl4_16)),
% 0.20/0.48    inference(resolution,[],[f101,f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl4_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f91])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    spl4_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f111])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl4_16 | ~spl4_7 | ~spl4_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f98,f95,f60,f100])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    spl4_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    spl4_15 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | (~spl4_7 | ~spl4_15)),
% 0.20/0.48    inference(resolution,[],[f96,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0) | ~spl4_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f60])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl4_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f95])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl4_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f33,f95])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    spl4_14 | ~spl4_10 | ~spl4_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f88,f81,f72,f91])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    spl4_12 <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_10 | ~spl4_12)),
% 0.20/0.48    inference(superposition,[],[f82,f73])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl4_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f81])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    spl4_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f28,f85])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl4_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f26,f81])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    spl4_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f34,f72])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl4_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f27,f68])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl4_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f25,f64])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl4_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f24,f60])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl4_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f22,f56])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (((~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    spl4_4 | ~spl4_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f17,f52,f49])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl4_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f45])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ~spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f41])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ~v1_partfun1(sK2,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    spl4_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f20,f37])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (26025)------------------------------
% 0.20/0.48  % (26025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (26025)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (26025)Memory used [KB]: 10618
% 0.20/0.48  % (26025)Time elapsed: 0.006 s
% 0.20/0.48  % (26025)------------------------------
% 0.20/0.48  % (26025)------------------------------
% 0.20/0.48  % (26015)Success in time 0.12 s
%------------------------------------------------------------------------------
