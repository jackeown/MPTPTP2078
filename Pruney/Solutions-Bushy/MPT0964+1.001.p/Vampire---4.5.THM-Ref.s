%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0964+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 134 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  234 ( 430 expanded)
%              Number of equality atoms :   54 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f59,f63,f67,f79,f83,f88,f92,f96,f101,f122,f135])).

fof(f135,plain,
    ( ~ spl7_1
    | ~ spl7_6
    | spl7_8
    | ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_6
    | spl7_8
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f133,f87])).

fof(f87,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl7_8
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f133,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f132,f78])).

fof(f78,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f132,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl7_1
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f130,f49])).

fof(f49,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f130,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl7_13 ),
    inference(resolution,[],[f121,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f121,plain,
    ( sP5(k1_funct_1(sK3,sK2),sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl7_13
  <=> sP5(k1_funct_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f122,plain,
    ( spl7_13
    | ~ spl7_2
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f107,f98,f53,f120])).

fof(f53,plain,
    ( spl7_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f98,plain,
    ( spl7_11
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f107,plain,
    ( sP5(k1_funct_1(sK3,sK2),sK3)
    | ~ spl7_2
    | ~ spl7_11 ),
    inference(resolution,[],[f102,f54])).

fof(f54,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sP5(k1_funct_1(sK3,X0),sK3) )
    | ~ spl7_11 ),
    inference(superposition,[],[f41,f99])).

fof(f99,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f98])).

fof(f41,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | sP5(k1_funct_1(X0,X3),X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,
    ( spl7_11
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f100,f94,f90,f98])).

fof(f90,plain,
    ( spl7_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f94,plain,
    ( spl7_10
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f100,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f95,f91])).

fof(f91,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f95,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( spl7_10
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f69,f65,f94])).

fof(f65,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f69,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f66,f37])).

fof(f37,plain,(
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

fof(f66,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f92,plain,
    ( spl7_9
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f75,f65,f61,f57,f90])).

fof(f57,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f61,plain,
    ( spl7_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f75,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f74,f62])).

fof(f62,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f74,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f71,f58])).

fof(f58,plain,
    ( k1_xboole_0 != sK1
    | spl7_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f71,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_5 ),
    inference(resolution,[],[f66,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f88,plain,
    ( ~ spl7_8
    | ~ spl7_5
    | spl7_7 ),
    inference(avatar_split_clause,[],[f84,f81,f65,f86])).

fof(f81,plain,
    ( spl7_7
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f84,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl7_5
    | spl7_7 ),
    inference(forward_demodulation,[],[f82,f72])).

fof(f72,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f66,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f82,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f22,f81])).

fof(f22,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f79,plain,
    ( spl7_6
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f68,f65,f77])).

fof(f68,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f66,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

% (26661)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (26646)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (26654)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f67,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f19,f65])).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f18,f61])).

fof(f18,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f21,f57])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f20,f53])).

fof(f20,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f17,f48])).

fof(f17,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
