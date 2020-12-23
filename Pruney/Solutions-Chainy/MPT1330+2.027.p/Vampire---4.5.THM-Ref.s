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
% DateTime   : Thu Dec  3 13:13:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 222 expanded)
%              Number of leaves         :   21 (  91 expanded)
%              Depth                    :   10
%              Number of atoms          :  310 ( 709 expanded)
%              Number of equality atoms :   85 ( 243 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f40,f46,f50,f56,f60,f67,f71,f77,f88,f92,f109,f119,f129,f133,f141,f153,f156])).

fof(f156,plain,
    ( spl3_17
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl3_17
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f154,f128])).

fof(f128,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_17
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f154,plain,
    ( k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f152,f149])).

fof(f149,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f143,f132])).

fof(f132,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_18
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f143,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_19 ),
    inference(resolution,[],[f140,f28])).

fof(f28,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f152,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl3_20
  <=> k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f153,plain,
    ( spl3_20
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f111,f75,f65,f62,f151])).

fof(f62,plain,
    ( spl3_7
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f65,plain,
    ( spl3_8
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f75,plain,
    ( spl3_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f111,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f110,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f110,plain,
    ( k1_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) = k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f81,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f81,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_10 ),
    inference(resolution,[],[f76,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f76,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f141,plain,
    ( spl3_19
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f114,f75,f65,f62,f139])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f112,f100])).

fof(f112,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(superposition,[],[f76,f63])).

fof(f133,plain,
    ( spl3_18
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f115,f65,f62,f58,f131])).

fof(f58,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f115,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f113,f100])).

fof(f113,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f59,f63])).

% (4637)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f59,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f129,plain,
    ( ~ spl3_17
    | ~ spl3_7
    | ~ spl3_8
    | spl3_16 ),
    inference(avatar_split_clause,[],[f121,f117,f65,f62,f127])).

fof(f117,plain,
    ( spl3_16
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f121,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_8
    | spl3_16 ),
    inference(forward_demodulation,[],[f120,f63])).

fof(f120,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl3_8
    | spl3_16 ),
    inference(forward_demodulation,[],[f118,f100])).

fof(f118,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,
    ( ~ spl3_16
    | ~ spl3_3
    | ~ spl3_5
    | spl3_12 ),
    inference(avatar_split_clause,[],[f94,f90,f54,f44,f117])).

fof(f44,plain,
    ( spl3_3
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( spl3_5
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f90,plain,
    ( spl3_12
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f94,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_3
    | ~ spl3_5
    | spl3_12 ),
    inference(forward_demodulation,[],[f93,f55])).

fof(f55,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f93,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_3
    | spl3_12 ),
    inference(forward_demodulation,[],[f91,f45])).

fof(f45,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f91,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f109,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | spl3_12 ),
    inference(subsumption_resolution,[],[f107,f94])).

fof(f107,plain,
    ( k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f81,f87])).

fof(f87,plain,
    ( k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_11
  <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f92,plain,(
    ~ spl3_12 ),
    inference(avatar_split_clause,[],[f16,f90])).

fof(f16,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

% (4646)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

fof(f88,plain,
    ( spl3_11
    | ~ spl3_6
    | spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f83,f75,f65,f58,f86])).

fof(f83,plain,
    ( k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_6
    | spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f82,f59])).

fof(f82,plain,
    ( k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f79,f66])).

fof(f66,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f79,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_10 ),
    inference(resolution,[],[f76,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f73,f69,f54,f44,f75])).

fof(f69,plain,
    ( spl3_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f73,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f72,f55])).

fof(f72,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f70,f45])).

fof(f70,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f15,f69])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,
    ( spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f13,f65,f62])).

fof(f13,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f52,f48,f44,f38,f58])).

fof(f38,plain,
    ( spl3_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,
    ( spl3_4
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f52,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f51,f42])).

fof(f42,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f39,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f39,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f51,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f49,f45])).

fof(f49,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f56,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f38,f54])).

fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f48])).

fof(f14,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f46,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f41,f34,f44])).

fof(f34,plain,
    ( spl3_1
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f35,f27])).

fof(f35,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:57:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (4629)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.46  % (4629)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f157,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f36,f40,f46,f50,f56,f60,f67,f71,f77,f88,f92,f109,f119,f129,f133,f141,f153,f156])).
% 0.22/0.46  fof(f156,plain,(
% 0.22/0.46    spl3_17 | ~spl3_18 | ~spl3_19 | ~spl3_20),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f155])).
% 0.22/0.46  fof(f155,plain,(
% 0.22/0.46    $false | (spl3_17 | ~spl3_18 | ~spl3_19 | ~spl3_20)),
% 0.22/0.46    inference(subsumption_resolution,[],[f154,f128])).
% 0.22/0.46  fof(f128,plain,(
% 0.22/0.46    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | spl3_17),
% 0.22/0.46    inference(avatar_component_clause,[],[f127])).
% 0.22/0.46  fof(f127,plain,(
% 0.22/0.46    spl3_17 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.46  fof(f154,plain,(
% 0.22/0.46    k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | (~spl3_18 | ~spl3_19 | ~spl3_20)),
% 0.22/0.46    inference(forward_demodulation,[],[f152,f149])).
% 0.22/0.46  fof(f149,plain,(
% 0.22/0.46    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl3_18 | ~spl3_19)),
% 0.22/0.46    inference(subsumption_resolution,[],[f143,f132])).
% 0.22/0.46  fof(f132,plain,(
% 0.22/0.46    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl3_18),
% 0.22/0.46    inference(avatar_component_clause,[],[f131])).
% 0.22/0.46  fof(f131,plain,(
% 0.22/0.46    spl3_18 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.46  fof(f143,plain,(
% 0.22/0.46    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl3_19),
% 0.22/0.46    inference(resolution,[],[f140,f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.22/0.46    inference(equality_resolution,[],[f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(flattening,[],[f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.47  fof(f140,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_19),
% 0.22/0.47    inference(avatar_component_clause,[],[f139])).
% 0.22/0.47  fof(f139,plain,(
% 0.22/0.47    spl3_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.47  fof(f152,plain,(
% 0.22/0.47    k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | ~spl3_20),
% 0.22/0.47    inference(avatar_component_clause,[],[f151])).
% 0.22/0.47  fof(f151,plain,(
% 0.22/0.47    spl3_20 <=> k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.47  fof(f153,plain,(
% 0.22/0.47    spl3_20 | ~spl3_7 | ~spl3_8 | ~spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f111,f75,f65,f62,f151])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl3_7 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    spl3_8 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    spl3_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | (~spl3_7 | ~spl3_8 | ~spl3_10)),
% 0.22/0.47    inference(forward_demodulation,[],[f110,f63])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f62])).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    k1_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) = k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,k1_xboole_0) | (~spl3_8 | ~spl3_10)),
% 0.22/0.47    inference(forward_demodulation,[],[f81,f100])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f65])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | ~spl3_10),
% 0.22/0.47    inference(resolution,[],[f76,f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f75])).
% 0.22/0.47  fof(f141,plain,(
% 0.22/0.47    spl3_19 | ~spl3_7 | ~spl3_8 | ~spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f114,f75,f65,f62,f139])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_7 | ~spl3_8 | ~spl3_10)),
% 0.22/0.47    inference(forward_demodulation,[],[f112,f100])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_10)),
% 0.22/0.47    inference(superposition,[],[f76,f63])).
% 0.22/0.47  fof(f133,plain,(
% 0.22/0.47    spl3_18 | ~spl3_6 | ~spl3_7 | ~spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f115,f65,f62,f58,f131])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    spl3_6 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.22/0.47    inference(forward_demodulation,[],[f113,f100])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    v1_funct_2(sK2,k1_xboole_0,k2_struct_0(sK1)) | (~spl3_6 | ~spl3_7)),
% 0.22/0.47    inference(superposition,[],[f59,f63])).
% 0.22/0.47  % (4637)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f58])).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    ~spl3_17 | ~spl3_7 | ~spl3_8 | spl3_16),
% 0.22/0.47    inference(avatar_split_clause,[],[f121,f117,f65,f62,f127])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    spl3_16 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | (~spl3_7 | ~spl3_8 | spl3_16)),
% 0.22/0.47    inference(forward_demodulation,[],[f120,f63])).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,k1_xboole_0) | (~spl3_8 | spl3_16)),
% 0.22/0.47    inference(forward_demodulation,[],[f118,f100])).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_16),
% 0.22/0.47    inference(avatar_component_clause,[],[f117])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    ~spl3_16 | ~spl3_3 | ~spl3_5 | spl3_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f94,f90,f54,f44,f117])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    spl3_3 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    spl3_5 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    spl3_12 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl3_3 | ~spl3_5 | spl3_12)),
% 0.22/0.47    inference(forward_demodulation,[],[f93,f55])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f54])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl3_3 | spl3_12)),
% 0.22/0.47    inference(forward_demodulation,[],[f91,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f44])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f90])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    ~spl3_3 | ~spl3_5 | ~spl3_10 | ~spl3_11 | spl3_12),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f108])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    $false | (~spl3_3 | ~spl3_5 | ~spl3_10 | ~spl3_11 | spl3_12)),
% 0.22/0.47    inference(subsumption_resolution,[],[f107,f94])).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl3_10 | ~spl3_11)),
% 0.22/0.47    inference(forward_demodulation,[],[f81,f87])).
% 0.22/0.47  fof(f87,plain,(
% 0.22/0.47    k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f86])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    spl3_11 <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    ~spl3_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f16,f90])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f7])).
% 0.22/0.47  % (4646)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.47    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.47  fof(f5,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f4])).
% 0.22/0.47  fof(f4,conjecture,(
% 0.22/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    spl3_11 | ~spl3_6 | spl3_8 | ~spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f83,f75,f65,f58,f86])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_6 | spl3_8 | ~spl3_10)),
% 0.22/0.47    inference(subsumption_resolution,[],[f82,f59])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (spl3_8 | ~spl3_10)),
% 0.22/0.47    inference(subsumption_resolution,[],[f79,f66])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    k1_xboole_0 != k2_struct_0(sK1) | spl3_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f65])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_10),
% 0.22/0.47    inference(resolution,[],[f76,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl3_10 | ~spl3_3 | ~spl3_5 | ~spl3_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f73,f69,f54,f44,f75])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    spl3_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_3 | ~spl3_5 | ~spl3_9)),
% 0.22/0.47    inference(forward_demodulation,[],[f72,f55])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_3 | ~spl3_9)),
% 0.22/0.47    inference(forward_demodulation,[],[f70,f45])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f69])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    spl3_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f15,f69])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    spl3_7 | ~spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f13,f65,f62])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    spl3_6 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f52,f48,f44,f38,f58])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl3_2 <=> l1_struct_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl3_4 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.47    inference(forward_demodulation,[],[f51,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_2),
% 0.22/0.47    inference(resolution,[],[f39,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    l1_struct_0(sK0) | ~spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f38])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_3 | ~spl3_4)),
% 0.22/0.47    inference(forward_demodulation,[],[f49,f45])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f48])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    spl3_5 | ~spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f42,f38,f54])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f14,f48])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    spl3_3 | ~spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f41,f34,f44])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    spl3_1 <=> l1_struct_0(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_1),
% 0.22/0.47    inference(resolution,[],[f35,f27])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    l1_struct_0(sK1) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f34])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f38])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    l1_struct_0(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f17,f34])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    l1_struct_0(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (4629)------------------------------
% 0.22/0.47  % (4629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (4629)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (4629)Memory used [KB]: 6140
% 0.22/0.47  % (4629)Time elapsed: 0.066 s
% 0.22/0.47  % (4629)------------------------------
% 0.22/0.47  % (4629)------------------------------
% 0.22/0.47  % (4627)Success in time 0.107 s
%------------------------------------------------------------------------------
