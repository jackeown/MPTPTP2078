%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 153 expanded)
%              Number of leaves         :   25 (  66 expanded)
%              Depth                    :    6
%              Number of atoms          :  308 ( 514 expanded)
%              Number of equality atoms :   50 (  85 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f52,f56,f60,f64,f68,f72,f76,f80,f84,f96,f102,f111,f139,f142,f157,f170,f188,f196])).

fof(f196,plain,
    ( ~ spl7_16
    | ~ spl7_31 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f194,f110])).

fof(f110,plain,
    ( r2_hidden(sK0,k9_relat_1(sK3,sK1))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_16
  <=> r2_hidden(sK0,k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

% (18335)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f194,plain,
    ( ~ r2_hidden(sK0,k9_relat_1(sK3,sK1))
    | ~ spl7_31 ),
    inference(equality_resolution,[],[f187])).

fof(f187,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK1)) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl7_31
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,sK1))
        | sK0 != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f188,plain,
    ( ~ spl7_23
    | spl7_31
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f180,f168,f78,f42,f186,f137])).

fof(f137,plain,
    ( spl7_23
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f42,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f78,plain,
    ( spl7_10
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f168,plain,
    ( spl7_28
  <=> ! [X1,X0] :
        ( sK0 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ r2_hidden(sK5(sK3,X1,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,sK1))
        | sK0 != X0
        | ~ v1_relat_1(sK3) )
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f179,f43])).

fof(f43,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,sK1))
        | sK0 != X0
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_10
    | ~ spl7_28 ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,sK1))
        | sK0 != X0
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK1)) )
    | ~ spl7_10
    | ~ spl7_28 ),
    inference(resolution,[],[f169,f79])).

fof(f79,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(sK5(X0,X1,X3),X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X3,k9_relat_1(X0,X1)) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(sK3,X1,X0),sK1)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | sK0 != X0 )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f168])).

fof(f170,plain,
    ( spl7_28
    | ~ spl7_7
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f163,f155,f66,f168])).

fof(f66,plain,
    ( spl7_7
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f155,plain,
    ( spl7_26
  <=> ! [X1,X0] :
        ( sK0 != X1
        | ~ m1_subset_1(sK5(sK3,X0,X1),sK1)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( sK0 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ r2_hidden(sK5(sK3,X1,X0),sK1) )
    | ~ spl7_7
    | ~ spl7_26 ),
    inference(resolution,[],[f156,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK3,X0,X1),sK1)
        | sK0 != X1
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,
    ( spl7_26
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f147,f134,f58,f155])).

fof(f58,plain,
    ( spl7_5
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | sK0 != k1_funct_1(sK3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f134,plain,
    ( spl7_22
  <=> ! [X1,X0] :
        ( k1_funct_1(sK3,sK5(sK3,X0,X1)) = X1
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( sK0 != X1
        | ~ m1_subset_1(sK5(sK3,X0,X1),sK1)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(superposition,[],[f59,f135])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK3,sK5(sK3,X0,X1)) = X1
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f134])).

fof(f59,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f142,plain,
    ( ~ spl7_3
    | ~ spl7_6
    | ~ spl7_8
    | spl7_23 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_8
    | spl7_23 ),
    inference(unit_resulting_resolution,[],[f63,f51,f138,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_8
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f138,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f137])).

fof(f51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f63,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl7_6
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f139,plain,
    ( spl7_22
    | ~ spl7_23
    | ~ spl7_1
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f120,f94,f42,f137,f134])).

fof(f94,plain,
    ( spl7_14
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(X0,sK5(X0,X1,X3)) = X3
        | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK3)
        | k1_funct_1(sK3,sK5(sK3,X0,X1)) = X1
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl7_1
    | ~ spl7_14 ),
    inference(resolution,[],[f95,f43])).

fof(f95,plain,
    ( ! [X0,X3,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(X0,sK5(X0,X1,X3)) = X3
        | ~ r2_hidden(X3,k9_relat_1(X0,X1)) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f111,plain,
    ( spl7_16
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f107,f100,f74,f54,f50,f109])).

fof(f54,plain,
    ( spl7_4
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f74,plain,
    ( spl7_9
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f100,plain,
    ( spl7_15
  <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f107,plain,
    ( r2_hidden(sK0,k9_relat_1(sK3,sK1))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f55,f105])).

fof(f105,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f103,f51])).

fof(f103,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(superposition,[],[f101,f75])).

fof(f75,plain,
    ( ! [X2,X0,X3,X1] :
        ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f101,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f55,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f102,plain,
    ( spl7_15
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f97,f82,f50,f100])).

fof(f82,plain,
    ( spl7_11
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f97,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(resolution,[],[f83,f51])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f82])).

fof(f96,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f38,f94])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK5(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK5(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f84,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f33,f82])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f80,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f72,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f22,f70])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f68,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f32,f66])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f64,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f31,f62])).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f60,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f17,f58])).

% (18331)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f17,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | sK0 != k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(f56,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:50:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (18317)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (18317)Refutation not found, incomplete strategy% (18317)------------------------------
% 0.20/0.48  % (18317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18325)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (18317)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18317)Memory used [KB]: 10618
% 0.20/0.49  % (18317)Time elapsed: 0.061 s
% 0.20/0.49  % (18317)------------------------------
% 0.20/0.49  % (18317)------------------------------
% 0.20/0.49  % (18327)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (18325)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f44,f52,f56,f60,f64,f68,f72,f76,f80,f84,f96,f102,f111,f139,f142,f157,f170,f188,f196])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ~spl7_16 | ~spl7_31),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f195])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    $false | (~spl7_16 | ~spl7_31)),
% 0.20/0.50    inference(subsumption_resolution,[],[f194,f110])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    r2_hidden(sK0,k9_relat_1(sK3,sK1)) | ~spl7_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f109])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    spl7_16 <=> r2_hidden(sK0,k9_relat_1(sK3,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.50  % (18335)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    ~r2_hidden(sK0,k9_relat_1(sK3,sK1)) | ~spl7_31),
% 0.20/0.50    inference(equality_resolution,[],[f187])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    ( ! [X0] : (sK0 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,sK1))) ) | ~spl7_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f186])).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    spl7_31 <=> ! [X0] : (~r2_hidden(X0,k9_relat_1(sK3,sK1)) | sK0 != X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    ~spl7_23 | spl7_31 | ~spl7_1 | ~spl7_10 | ~spl7_28),
% 0.20/0.50    inference(avatar_split_clause,[],[f180,f168,f78,f42,f186,f137])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    spl7_23 <=> v1_relat_1(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    spl7_1 <=> v1_funct_1(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    spl7_10 <=> ! [X1,X3,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,k9_relat_1(X0,X1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    spl7_28 <=> ! [X1,X0] : (sK0 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~r2_hidden(sK5(sK3,X1,X0),sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK3,sK1)) | sK0 != X0 | ~v1_relat_1(sK3)) ) | (~spl7_1 | ~spl7_10 | ~spl7_28)),
% 0.20/0.50    inference(subsumption_resolution,[],[f179,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    v1_funct_1(sK3) | ~spl7_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f42])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK3,sK1)) | sK0 != X0 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | (~spl7_10 | ~spl7_28)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f178])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK3,sK1)) | sK0 != X0 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r2_hidden(X0,k9_relat_1(sK3,sK1))) ) | (~spl7_10 | ~spl7_28)),
% 0.20/0.50    inference(resolution,[],[f169,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X3,k9_relat_1(X0,X1))) ) | ~spl7_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f78])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(sK5(sK3,X1,X0),sK1) | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | sK0 != X0) ) | ~spl7_28),
% 0.20/0.50    inference(avatar_component_clause,[],[f168])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    spl7_28 | ~spl7_7 | ~spl7_26),
% 0.20/0.50    inference(avatar_split_clause,[],[f163,f155,f66,f168])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    spl7_7 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    spl7_26 <=> ! [X1,X0] : (sK0 != X1 | ~m1_subset_1(sK5(sK3,X0,X1),sK1) | ~r2_hidden(X1,k9_relat_1(sK3,X0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK0 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~r2_hidden(sK5(sK3,X1,X0),sK1)) ) | (~spl7_7 | ~spl7_26)),
% 0.20/0.50    inference(resolution,[],[f156,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) ) | ~spl7_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f66])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK5(sK3,X0,X1),sK1) | sK0 != X1 | ~r2_hidden(X1,k9_relat_1(sK3,X0))) ) | ~spl7_26),
% 0.20/0.50    inference(avatar_component_clause,[],[f155])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    spl7_26 | ~spl7_5 | ~spl7_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f147,f134,f58,f155])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    spl7_5 <=> ! [X4] : (~m1_subset_1(X4,sK1) | sK0 != k1_funct_1(sK3,X4))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    spl7_22 <=> ! [X1,X0] : (k1_funct_1(sK3,sK5(sK3,X0,X1)) = X1 | ~r2_hidden(X1,k9_relat_1(sK3,X0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK0 != X1 | ~m1_subset_1(sK5(sK3,X0,X1),sK1) | ~r2_hidden(X1,k9_relat_1(sK3,X0))) ) | (~spl7_5 | ~spl7_22)),
% 0.20/0.50    inference(superposition,[],[f59,f135])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_funct_1(sK3,sK5(sK3,X0,X1)) = X1 | ~r2_hidden(X1,k9_relat_1(sK3,X0))) ) | ~spl7_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f134])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) ) | ~spl7_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f58])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    ~spl7_3 | ~spl7_6 | ~spl7_8 | spl7_23),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f140])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    $false | (~spl7_3 | ~spl7_6 | ~spl7_8 | spl7_23)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f63,f51,f138,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl7_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    spl7_8 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ~v1_relat_1(sK3) | spl7_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f137])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl7_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    spl7_6 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    spl7_22 | ~spl7_23 | ~spl7_1 | ~spl7_14),
% 0.20/0.50    inference(avatar_split_clause,[],[f120,f94,f42,f137,f134])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    spl7_14 <=> ! [X1,X3,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK5(X0,X1,X3)) = X3 | ~r2_hidden(X3,k9_relat_1(X0,X1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(sK3) | k1_funct_1(sK3,sK5(sK3,X0,X1)) = X1 | ~r2_hidden(X1,k9_relat_1(sK3,X0))) ) | (~spl7_1 | ~spl7_14)),
% 0.20/0.50    inference(resolution,[],[f95,f43])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK5(X0,X1,X3)) = X3 | ~r2_hidden(X3,k9_relat_1(X0,X1))) ) | ~spl7_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f94])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl7_16 | ~spl7_3 | ~spl7_4 | ~spl7_9 | ~spl7_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f107,f100,f74,f54,f50,f109])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    spl7_4 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    spl7_9 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    spl7_15 <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    r2_hidden(sK0,k9_relat_1(sK3,sK1)) | (~spl7_3 | ~spl7_4 | ~spl7_9 | ~spl7_15)),
% 0.20/0.50    inference(backward_demodulation,[],[f55,f105])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | (~spl7_3 | ~spl7_9 | ~spl7_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f103,f51])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl7_9 | ~spl7_15)),
% 0.20/0.50    inference(superposition,[],[f101,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f74])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | ~spl7_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f100])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl7_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f54])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    spl7_15 | ~spl7_3 | ~spl7_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f97,f82,f50,f100])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    spl7_11 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | (~spl7_3 | ~spl7_11)),
% 0.20/0.50    inference(resolution,[],[f83,f51])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) ) | ~spl7_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f82])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    spl7_14),
% 0.20/0.50    inference(avatar_split_clause,[],[f38,f94])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK5(X0,X1,X3)) = X3 | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.20/0.50    inference(equality_resolution,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK5(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl7_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f33,f82])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    spl7_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f39,f78])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.20/0.50    inference(equality_resolution,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl7_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f35,f74])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl7_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f22,f70])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    spl7_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f32,f66])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    spl7_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f31,f62])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    spl7_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f17,f58])).
% 0.20/0.50  % (18331)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ( ! [X4] : (~m1_subset_1(X4,sK1) | sK0 != k1_funct_1(sK3,X4)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.20/0.50    inference(negated_conjecture,[],[f7])).
% 0.20/0.50  fof(f7,conjecture,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    spl7_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f21,f54])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f20,f50])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    spl7_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f18,f42])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    v1_funct_1(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (18325)------------------------------
% 0.20/0.50  % (18325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (18325)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (18325)Memory used [KB]: 10746
% 0.20/0.50  % (18325)Time elapsed: 0.077 s
% 0.20/0.50  % (18325)------------------------------
% 0.20/0.50  % (18325)------------------------------
% 0.20/0.50  % (18315)Success in time 0.137 s
%------------------------------------------------------------------------------
