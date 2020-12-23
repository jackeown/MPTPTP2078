%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:07 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  167 (1107 expanded)
%              Number of leaves         :   26 ( 289 expanded)
%              Depth                    :   20
%              Number of atoms          :  585 (6123 expanded)
%              Number of equality atoms :   80 ( 897 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1681,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f150,f191,f194,f469,f475,f635,f641,f681,f1001,f1675])).

fof(f1675,plain,
    ( spl6_3
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f1674])).

fof(f1674,plain,
    ( $false
    | spl6_3
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f1666,f226])).

fof(f226,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f225,f169])).

fof(f169,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f54])).

fof(f54,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f225,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f167,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f167,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f65,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1666,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl6_3
    | ~ spl6_30 ),
    inference(resolution,[],[f640,f137])).

fof(f137,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f640,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(k1_relat_1(sK2),X1) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f639])).

fof(f639,plain,
    ( spl6_30
  <=> ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f1001,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f1000])).

fof(f1000,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f994,f732])).

fof(f732,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl6_2
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f649,f708])).

fof(f708,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f653,f707])).

fof(f707,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f464,f474])).

fof(f474,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl6_19
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f464,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl6_17
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f653,plain,
    ( sK1 = k1_relat_1(k1_xboole_0)
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f199,f474])).

fof(f199,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f198,f187])).

fof(f187,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f168,f67])).

fof(f67,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f168,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f65,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f198,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f197,f169])).

fof(f197,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f161,f63])).

fof(f63,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f161,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f66,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f649,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,sK0)
    | spl6_2
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f133,f474])).

fof(f133,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f994,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(resolution,[],[f960,f682])).

fof(f682,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f226,f467])).

fof(f467,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl6_18
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f960,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f959,f648])).

fof(f648,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f128,f474])).

fof(f128,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f959,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f950,f742])).

fof(f742,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f699,f708])).

fof(f699,plain,
    ( v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f656,f467])).

fof(f656,plain,
    ( v1_funct_2(k1_xboole_0,sK1,k1_relat_1(sK2))
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f376,f474])).

fof(f376,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f218,f199])).

fof(f218,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f217,f196])).

fof(f196,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f195,f169])).

fof(f195,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f162,f63])).

fof(f162,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f217,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f214,f149])).

fof(f149,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f214,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f128,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f950,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(resolution,[],[f743,f120])).

fof(f120,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_tarski(X1,X2)
      | v1_funct_2(X3,k1_xboole_0,X2)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f743,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f700,f708])).

fof(f700,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f657,f467])).

fof(f657,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f377,f474])).

fof(f377,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f221,f199])).

fof(f221,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f220,f196])).

fof(f220,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f215,f149])).

fof(f215,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f128,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f681,plain,
    ( spl6_3
    | ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f680])).

fof(f680,plain,
    ( $false
    | spl6_3
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f678,f69])).

fof(f69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f678,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f620,f474])).

fof(f620,plain,
    ( ~ v1_xboole_0(k2_funct_1(sK2))
    | spl6_3 ),
    inference(resolution,[],[f477,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f477,plain,
    ( r2_hidden(sK3(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)),k2_funct_1(sK2))
    | spl6_3 ),
    inference(resolution,[],[f425,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f425,plain,
    ( ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0))
    | spl6_3 ),
    inference(resolution,[],[f137,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f641,plain,
    ( spl6_30
    | spl6_18
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f637,f147,f127,f466,f639])).

fof(f637,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_relat_1(sK2)
        | ~ r1_tarski(k1_relat_1(sK2),X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f636,f128])).

fof(f636,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_relat_1(sK2)
        | ~ r1_tarski(k1_relat_1(sK2),X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f514,f376])).

fof(f514,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_relat_1(sK2)
        | ~ r1_tarski(k1_relat_1(sK2),X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(resolution,[],[f377,f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f635,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f634])).

fof(f634,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | spl6_18 ),
    inference(subsumption_resolution,[],[f631,f133])).

fof(f631,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl6_1
    | ~ spl6_5
    | spl6_18 ),
    inference(resolution,[],[f522,f226])).

fof(f522,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | v1_funct_2(k2_funct_1(sK2),sK1,X0) )
    | ~ spl6_1
    | ~ spl6_5
    | spl6_18 ),
    inference(subsumption_resolution,[],[f521,f128])).

fof(f521,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl6_1
    | ~ spl6_5
    | spl6_18 ),
    inference(subsumption_resolution,[],[f520,f376])).

fof(f520,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl6_1
    | ~ spl6_5
    | spl6_18 ),
    inference(subsumption_resolution,[],[f513,f468])).

fof(f468,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f466])).

fof(f513,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(sK2)
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(resolution,[],[f377,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | v1_funct_2(X3,X0,X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f475,plain,
    ( spl6_19
    | ~ spl6_18
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f470,f147,f466,f472])).

fof(f470,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f459,f149])).

fof(f459,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f80,f196])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f469,plain,
    ( spl6_17
    | ~ spl6_18
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f460,f147,f466,f462])).

fof(f460,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f458,f149])).

fof(f458,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f82,f196])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f194,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f192,f169])).

fof(f192,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f163,f63])).

fof(f163,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl6_1 ),
    inference(resolution,[],[f129,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f129,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f127])).

fof(f191,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f169,f145])).

fof(f145,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f150,plain,
    ( ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f139,f147,f143])).

fof(f139,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f63,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f138,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f68,f135,f131,f127])).

fof(f68,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:17:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (5369)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (5377)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (5375)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (5391)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (5393)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (5383)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (5385)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (5376)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (5384)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (5388)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (5371)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (5379)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (5397)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.55  % (5394)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.55  % (5395)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.55  % (5398)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.55  % (5386)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  % (5370)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.55  % (5374)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.41/0.55  % (5396)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (5389)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.56  % (5386)Refutation not found, incomplete strategy% (5386)------------------------------
% 1.41/0.56  % (5386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (5386)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (5386)Memory used [KB]: 10746
% 1.41/0.56  % (5386)Time elapsed: 0.094 s
% 1.41/0.56  % (5386)------------------------------
% 1.41/0.56  % (5386)------------------------------
% 1.41/0.56  % (5373)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.56  % (5372)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.56  % (5382)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.56  % (5378)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.56  % (5380)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.57  % (5381)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.57  % (5392)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.52/0.57  % (5390)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.52/0.57  % (5387)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.52/0.58  % (5377)Refutation found. Thanks to Tanya!
% 1.52/0.58  % SZS status Theorem for theBenchmark
% 1.52/0.59  % (5391)Refutation not found, incomplete strategy% (5391)------------------------------
% 1.52/0.59  % (5391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.59  % (5391)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.59  
% 1.52/0.59  % (5391)Memory used [KB]: 11001
% 1.52/0.59  % (5391)Time elapsed: 0.166 s
% 1.52/0.59  % (5391)------------------------------
% 1.52/0.59  % (5391)------------------------------
% 1.52/0.60  % SZS output start Proof for theBenchmark
% 1.52/0.60  fof(f1681,plain,(
% 1.52/0.60    $false),
% 1.52/0.60    inference(avatar_sat_refutation,[],[f138,f150,f191,f194,f469,f475,f635,f641,f681,f1001,f1675])).
% 1.52/0.60  fof(f1675,plain,(
% 1.52/0.60    spl6_3 | ~spl6_30),
% 1.52/0.60    inference(avatar_contradiction_clause,[],[f1674])).
% 1.52/0.60  fof(f1674,plain,(
% 1.52/0.60    $false | (spl6_3 | ~spl6_30)),
% 1.52/0.60    inference(subsumption_resolution,[],[f1666,f226])).
% 1.52/0.60  fof(f226,plain,(
% 1.52/0.60    r1_tarski(k1_relat_1(sK2),sK0)),
% 1.52/0.60    inference(subsumption_resolution,[],[f225,f169])).
% 1.52/0.60  fof(f169,plain,(
% 1.52/0.60    v1_relat_1(sK2)),
% 1.52/0.60    inference(resolution,[],[f65,f100])).
% 1.52/0.60  fof(f100,plain,(
% 1.52/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f47])).
% 1.52/0.60  fof(f47,plain,(
% 1.52/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.60    inference(ennf_transformation,[],[f16])).
% 1.52/0.60  fof(f16,axiom,(
% 1.52/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.52/0.60  fof(f65,plain,(
% 1.52/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.52/0.60    inference(cnf_transformation,[],[f55])).
% 1.52/0.60  fof(f55,plain,(
% 1.52/0.60    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.52/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f54])).
% 1.52/0.60  fof(f54,plain,(
% 1.52/0.60    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f29,plain,(
% 1.52/0.60    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.52/0.60    inference(flattening,[],[f28])).
% 1.52/0.60  fof(f28,plain,(
% 1.52/0.60    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.52/0.60    inference(ennf_transformation,[],[f25])).
% 1.52/0.60  fof(f25,negated_conjecture,(
% 1.52/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.52/0.60    inference(negated_conjecture,[],[f24])).
% 1.52/0.60  fof(f24,conjecture,(
% 1.52/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.52/0.60  fof(f225,plain,(
% 1.52/0.60    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 1.52/0.60    inference(resolution,[],[f167,f93])).
% 1.52/0.60  fof(f93,plain,(
% 1.52/0.60    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f57])).
% 1.52/0.60  fof(f57,plain,(
% 1.52/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.52/0.60    inference(nnf_transformation,[],[f45])).
% 1.52/0.60  fof(f45,plain,(
% 1.52/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.52/0.60    inference(ennf_transformation,[],[f5])).
% 1.52/0.60  fof(f5,axiom,(
% 1.52/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.52/0.60  fof(f167,plain,(
% 1.52/0.60    v4_relat_1(sK2,sK0)),
% 1.52/0.60    inference(resolution,[],[f65,f102])).
% 1.52/0.60  fof(f102,plain,(
% 1.52/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f49])).
% 1.52/0.60  fof(f49,plain,(
% 1.52/0.60    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.60    inference(ennf_transformation,[],[f27])).
% 1.52/0.60  fof(f27,plain,(
% 1.52/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.52/0.60    inference(pure_predicate_removal,[],[f17])).
% 1.52/0.60  fof(f17,axiom,(
% 1.52/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.52/0.60  fof(f1666,plain,(
% 1.52/0.60    ~r1_tarski(k1_relat_1(sK2),sK0) | (spl6_3 | ~spl6_30)),
% 1.52/0.60    inference(resolution,[],[f640,f137])).
% 1.52/0.60  fof(f137,plain,(
% 1.52/0.60    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_3),
% 1.52/0.60    inference(avatar_component_clause,[],[f135])).
% 1.52/0.60  fof(f135,plain,(
% 1.52/0.60    spl6_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.52/0.60  fof(f640,plain,(
% 1.52/0.60    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k1_relat_1(sK2),X1)) ) | ~spl6_30),
% 1.52/0.60    inference(avatar_component_clause,[],[f639])).
% 1.52/0.60  fof(f639,plain,(
% 1.52/0.60    spl6_30 <=> ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.52/0.60  fof(f1001,plain,(
% 1.52/0.60    ~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_19),
% 1.52/0.60    inference(avatar_contradiction_clause,[],[f1000])).
% 1.52/0.60  fof(f1000,plain,(
% 1.52/0.60    $false | (~spl6_1 | spl6_2 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_19)),
% 1.52/0.60    inference(subsumption_resolution,[],[f994,f732])).
% 1.52/0.60  fof(f732,plain,(
% 1.52/0.60    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl6_2 | ~spl6_17 | ~spl6_19)),
% 1.52/0.60    inference(backward_demodulation,[],[f649,f708])).
% 1.52/0.60  fof(f708,plain,(
% 1.52/0.60    k1_xboole_0 = sK1 | (~spl6_17 | ~spl6_19)),
% 1.52/0.60    inference(backward_demodulation,[],[f653,f707])).
% 1.52/0.60  fof(f707,plain,(
% 1.52/0.60    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl6_17 | ~spl6_19)),
% 1.52/0.60    inference(forward_demodulation,[],[f464,f474])).
% 1.52/0.60  fof(f474,plain,(
% 1.52/0.60    k1_xboole_0 = k2_funct_1(sK2) | ~spl6_19),
% 1.52/0.60    inference(avatar_component_clause,[],[f472])).
% 1.52/0.60  fof(f472,plain,(
% 1.52/0.60    spl6_19 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.52/0.60  fof(f464,plain,(
% 1.52/0.60    k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~spl6_17),
% 1.52/0.60    inference(avatar_component_clause,[],[f462])).
% 1.52/0.60  fof(f462,plain,(
% 1.52/0.60    spl6_17 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.52/0.60  fof(f653,plain,(
% 1.52/0.60    sK1 = k1_relat_1(k1_xboole_0) | ~spl6_19),
% 1.52/0.60    inference(backward_demodulation,[],[f199,f474])).
% 1.52/0.60  fof(f199,plain,(
% 1.52/0.60    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 1.52/0.60    inference(forward_demodulation,[],[f198,f187])).
% 1.52/0.60  fof(f187,plain,(
% 1.52/0.60    sK1 = k2_relat_1(sK2)),
% 1.52/0.60    inference(forward_demodulation,[],[f168,f67])).
% 1.52/0.60  fof(f67,plain,(
% 1.52/0.60    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.52/0.60    inference(cnf_transformation,[],[f55])).
% 1.52/0.60  fof(f168,plain,(
% 1.52/0.60    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.52/0.60    inference(resolution,[],[f65,f101])).
% 1.52/0.60  fof(f101,plain,(
% 1.52/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f48])).
% 1.52/0.60  fof(f48,plain,(
% 1.52/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.60    inference(ennf_transformation,[],[f18])).
% 1.52/0.60  fof(f18,axiom,(
% 1.52/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.52/0.60  fof(f198,plain,(
% 1.52/0.60    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.52/0.60    inference(subsumption_resolution,[],[f197,f169])).
% 1.52/0.60  fof(f197,plain,(
% 1.52/0.60    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.52/0.60    inference(subsumption_resolution,[],[f161,f63])).
% 1.52/0.60  fof(f63,plain,(
% 1.52/0.60    v1_funct_1(sK2)),
% 1.52/0.60    inference(cnf_transformation,[],[f55])).
% 1.52/0.60  fof(f161,plain,(
% 1.52/0.60    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.52/0.60    inference(resolution,[],[f66,f88])).
% 1.52/0.60  fof(f88,plain,(
% 1.52/0.60    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f39])).
% 1.52/0.60  fof(f39,plain,(
% 1.52/0.60    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(flattening,[],[f38])).
% 1.52/0.60  fof(f38,plain,(
% 1.52/0.60    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.60    inference(ennf_transformation,[],[f14])).
% 1.52/0.60  fof(f14,axiom,(
% 1.52/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.52/0.60  fof(f66,plain,(
% 1.52/0.60    v2_funct_1(sK2)),
% 1.52/0.60    inference(cnf_transformation,[],[f55])).
% 1.52/0.60  fof(f649,plain,(
% 1.52/0.60    ~v1_funct_2(k1_xboole_0,sK1,sK0) | (spl6_2 | ~spl6_19)),
% 1.52/0.60    inference(backward_demodulation,[],[f133,f474])).
% 1.52/0.60  fof(f133,plain,(
% 1.52/0.60    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl6_2),
% 1.52/0.60    inference(avatar_component_clause,[],[f131])).
% 1.52/0.60  fof(f131,plain,(
% 1.52/0.60    spl6_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.52/0.60  fof(f994,plain,(
% 1.52/0.60    v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (~spl6_1 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_19)),
% 1.52/0.60    inference(resolution,[],[f960,f682])).
% 1.52/0.60  fof(f682,plain,(
% 1.52/0.60    r1_tarski(k1_xboole_0,sK0) | ~spl6_18),
% 1.52/0.60    inference(backward_demodulation,[],[f226,f467])).
% 1.52/0.60  fof(f467,plain,(
% 1.52/0.60    k1_xboole_0 = k1_relat_1(sK2) | ~spl6_18),
% 1.52/0.60    inference(avatar_component_clause,[],[f466])).
% 1.52/0.60  fof(f466,plain,(
% 1.52/0.60    spl6_18 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.52/0.60  fof(f960,plain,(
% 1.52/0.60    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl6_1 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_19)),
% 1.52/0.60    inference(subsumption_resolution,[],[f959,f648])).
% 1.52/0.60  fof(f648,plain,(
% 1.52/0.60    v1_funct_1(k1_xboole_0) | (~spl6_1 | ~spl6_19)),
% 1.52/0.60    inference(backward_demodulation,[],[f128,f474])).
% 1.52/0.60  fof(f128,plain,(
% 1.52/0.60    v1_funct_1(k2_funct_1(sK2)) | ~spl6_1),
% 1.52/0.60    inference(avatar_component_clause,[],[f127])).
% 1.52/0.60  fof(f127,plain,(
% 1.52/0.60    spl6_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.52/0.60  fof(f959,plain,(
% 1.52/0.60    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0)) ) | (~spl6_1 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_19)),
% 1.52/0.60    inference(subsumption_resolution,[],[f950,f742])).
% 1.52/0.60  fof(f742,plain,(
% 1.52/0.60    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_1 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_19)),
% 1.52/0.60    inference(backward_demodulation,[],[f699,f708])).
% 1.52/0.60  fof(f699,plain,(
% 1.52/0.60    v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | (~spl6_1 | ~spl6_5 | ~spl6_18 | ~spl6_19)),
% 1.52/0.60    inference(backward_demodulation,[],[f656,f467])).
% 1.52/0.60  fof(f656,plain,(
% 1.52/0.60    v1_funct_2(k1_xboole_0,sK1,k1_relat_1(sK2)) | (~spl6_1 | ~spl6_5 | ~spl6_19)),
% 1.52/0.60    inference(backward_demodulation,[],[f376,f474])).
% 1.52/0.60  fof(f376,plain,(
% 1.52/0.60    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl6_1 | ~spl6_5)),
% 1.52/0.60    inference(backward_demodulation,[],[f218,f199])).
% 1.52/0.60  fof(f218,plain,(
% 1.52/0.60    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl6_1 | ~spl6_5)),
% 1.52/0.60    inference(forward_demodulation,[],[f217,f196])).
% 1.52/0.60  fof(f196,plain,(
% 1.52/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.52/0.60    inference(subsumption_resolution,[],[f195,f169])).
% 1.52/0.60  fof(f195,plain,(
% 1.52/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.52/0.60    inference(subsumption_resolution,[],[f162,f63])).
% 1.52/0.60  fof(f162,plain,(
% 1.52/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.52/0.60    inference(resolution,[],[f66,f89])).
% 1.52/0.60  fof(f89,plain,(
% 1.52/0.60    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f39])).
% 1.52/0.60  fof(f217,plain,(
% 1.52/0.60    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl6_1 | ~spl6_5)),
% 1.52/0.60    inference(subsumption_resolution,[],[f214,f149])).
% 1.52/0.60  fof(f149,plain,(
% 1.52/0.60    v1_relat_1(k2_funct_1(sK2)) | ~spl6_5),
% 1.52/0.60    inference(avatar_component_clause,[],[f147])).
% 1.52/0.60  fof(f147,plain,(
% 1.52/0.60    spl6_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.52/0.60  fof(f214,plain,(
% 1.52/0.60    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl6_1),
% 1.52/0.60    inference(resolution,[],[f128,f84])).
% 1.52/0.60  fof(f84,plain,(
% 1.52/0.60    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f35])).
% 1.52/0.60  fof(f35,plain,(
% 1.52/0.60    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(flattening,[],[f34])).
% 1.52/0.60  fof(f34,plain,(
% 1.52/0.60    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.60    inference(ennf_transformation,[],[f22])).
% 1.52/0.60  fof(f22,axiom,(
% 1.52/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.52/0.60  fof(f950,plain,(
% 1.52/0.60    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0)) ) | (~spl6_1 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_19)),
% 1.52/0.60    inference(resolution,[],[f743,f120])).
% 1.52/0.60  fof(f120,plain,(
% 1.52/0.60    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_tarski(X1,X2) | v1_funct_2(X3,k1_xboole_0,X2) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 1.52/0.60    inference(equality_resolution,[],[f108])).
% 1.52/0.60  fof(f108,plain,(
% 1.52/0.60    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f53])).
% 1.52/0.60  fof(f53,plain,(
% 1.52/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.52/0.60    inference(flattening,[],[f52])).
% 1.52/0.60  fof(f52,plain,(
% 1.52/0.60    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.52/0.60    inference(ennf_transformation,[],[f23])).
% 1.52/0.60  fof(f23,axiom,(
% 1.52/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 1.52/0.60  fof(f743,plain,(
% 1.52/0.60    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_1 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_19)),
% 1.52/0.60    inference(backward_demodulation,[],[f700,f708])).
% 1.52/0.60  fof(f700,plain,(
% 1.52/0.60    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl6_1 | ~spl6_5 | ~spl6_18 | ~spl6_19)),
% 1.52/0.60    inference(backward_demodulation,[],[f657,f467])).
% 1.52/0.60  fof(f657,plain,(
% 1.52/0.60    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl6_1 | ~spl6_5 | ~spl6_19)),
% 1.52/0.60    inference(backward_demodulation,[],[f377,f474])).
% 1.52/0.60  fof(f377,plain,(
% 1.52/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl6_1 | ~spl6_5)),
% 1.52/0.60    inference(backward_demodulation,[],[f221,f199])).
% 1.52/0.60  fof(f221,plain,(
% 1.52/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl6_1 | ~spl6_5)),
% 1.52/0.60    inference(forward_demodulation,[],[f220,f196])).
% 1.52/0.60  fof(f220,plain,(
% 1.52/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl6_1 | ~spl6_5)),
% 1.52/0.60    inference(subsumption_resolution,[],[f215,f149])).
% 1.52/0.60  fof(f215,plain,(
% 1.52/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl6_1),
% 1.52/0.60    inference(resolution,[],[f128,f85])).
% 1.52/0.60  fof(f85,plain,(
% 1.52/0.60    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f35])).
% 1.52/0.60  fof(f681,plain,(
% 1.52/0.60    spl6_3 | ~spl6_19),
% 1.52/0.60    inference(avatar_contradiction_clause,[],[f680])).
% 1.52/0.60  fof(f680,plain,(
% 1.52/0.60    $false | (spl6_3 | ~spl6_19)),
% 1.52/0.60    inference(subsumption_resolution,[],[f678,f69])).
% 1.52/0.60  fof(f69,plain,(
% 1.52/0.60    v1_xboole_0(k1_xboole_0)),
% 1.52/0.60    inference(cnf_transformation,[],[f3])).
% 1.52/0.60  fof(f3,axiom,(
% 1.52/0.60    v1_xboole_0(k1_xboole_0)),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.52/0.60  fof(f678,plain,(
% 1.52/0.60    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_19)),
% 1.52/0.60    inference(backward_demodulation,[],[f620,f474])).
% 1.52/0.60  fof(f620,plain,(
% 1.52/0.60    ~v1_xboole_0(k2_funct_1(sK2)) | spl6_3),
% 1.52/0.60    inference(resolution,[],[f477,f92])).
% 1.52/0.60  fof(f92,plain,(
% 1.52/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f44])).
% 1.52/0.60  fof(f44,plain,(
% 1.52/0.60    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.52/0.60    inference(ennf_transformation,[],[f26])).
% 1.52/0.60  fof(f26,plain,(
% 1.52/0.60    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.52/0.60    inference(unused_predicate_definition_removal,[],[f1])).
% 1.52/0.60  fof(f1,axiom,(
% 1.52/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.52/0.60  fof(f477,plain,(
% 1.52/0.60    r2_hidden(sK3(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)),k2_funct_1(sK2)) | spl6_3),
% 1.52/0.60    inference(resolution,[],[f425,f96])).
% 1.52/0.60  fof(f96,plain,(
% 1.52/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f61])).
% 1.52/0.60  fof(f61,plain,(
% 1.52/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f59,f60])).
% 1.52/0.60  fof(f60,plain,(
% 1.52/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.52/0.60    introduced(choice_axiom,[])).
% 1.52/0.60  fof(f59,plain,(
% 1.52/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.60    inference(rectify,[],[f58])).
% 1.52/0.60  fof(f58,plain,(
% 1.52/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.60    inference(nnf_transformation,[],[f46])).
% 1.52/0.60  fof(f46,plain,(
% 1.52/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.60    inference(ennf_transformation,[],[f2])).
% 1.52/0.60  fof(f2,axiom,(
% 1.52/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.60  fof(f425,plain,(
% 1.52/0.60    ~r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) | spl6_3),
% 1.52/0.60    inference(resolution,[],[f137,f99])).
% 1.52/0.60  fof(f99,plain,(
% 1.52/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f62])).
% 1.52/0.60  fof(f62,plain,(
% 1.52/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.52/0.60    inference(nnf_transformation,[],[f4])).
% 1.52/0.60  fof(f4,axiom,(
% 1.52/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.52/0.60  fof(f641,plain,(
% 1.52/0.60    spl6_30 | spl6_18 | ~spl6_1 | ~spl6_5),
% 1.52/0.60    inference(avatar_split_clause,[],[f637,f147,f127,f466,f639])).
% 1.52/0.60  fof(f637,plain,(
% 1.52/0.60    ( ! [X1] : (k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl6_1 | ~spl6_5)),
% 1.52/0.60    inference(subsumption_resolution,[],[f636,f128])).
% 1.52/0.60  fof(f636,plain,(
% 1.52/0.60    ( ! [X1] : (k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(k2_funct_1(sK2))) ) | (~spl6_1 | ~spl6_5)),
% 1.52/0.60    inference(subsumption_resolution,[],[f514,f376])).
% 1.52/0.60  fof(f514,plain,(
% 1.52/0.60    ( ! [X1] : (k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))) ) | (~spl6_1 | ~spl6_5)),
% 1.52/0.60    inference(resolution,[],[f377,f109])).
% 1.52/0.60  fof(f109,plain,(
% 1.52/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f53])).
% 1.52/0.60  fof(f635,plain,(
% 1.52/0.60    ~spl6_1 | spl6_2 | ~spl6_5 | spl6_18),
% 1.52/0.60    inference(avatar_contradiction_clause,[],[f634])).
% 1.52/0.60  fof(f634,plain,(
% 1.52/0.60    $false | (~spl6_1 | spl6_2 | ~spl6_5 | spl6_18)),
% 1.52/0.60    inference(subsumption_resolution,[],[f631,f133])).
% 1.52/0.60  fof(f631,plain,(
% 1.52/0.60    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl6_1 | ~spl6_5 | spl6_18)),
% 1.52/0.60    inference(resolution,[],[f522,f226])).
% 1.52/0.60  fof(f522,plain,(
% 1.52/0.60    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) ) | (~spl6_1 | ~spl6_5 | spl6_18)),
% 1.52/0.60    inference(subsumption_resolution,[],[f521,f128])).
% 1.52/0.60  fof(f521,plain,(
% 1.52/0.60    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v1_funct_1(k2_funct_1(sK2))) ) | (~spl6_1 | ~spl6_5 | spl6_18)),
% 1.52/0.60    inference(subsumption_resolution,[],[f520,f376])).
% 1.52/0.60  fof(f520,plain,(
% 1.52/0.60    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))) ) | (~spl6_1 | ~spl6_5 | spl6_18)),
% 1.52/0.60    inference(subsumption_resolution,[],[f513,f468])).
% 1.52/0.60  fof(f468,plain,(
% 1.52/0.60    k1_xboole_0 != k1_relat_1(sK2) | spl6_18),
% 1.52/0.60    inference(avatar_component_clause,[],[f466])).
% 1.52/0.60  fof(f513,plain,(
% 1.52/0.60    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))) ) | (~spl6_1 | ~spl6_5)),
% 1.52/0.60    inference(resolution,[],[f377,f107])).
% 1.52/0.60  fof(f107,plain,(
% 1.52/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | v1_funct_2(X3,X0,X2) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f53])).
% 1.52/0.60  fof(f475,plain,(
% 1.52/0.60    spl6_19 | ~spl6_18 | ~spl6_5),
% 1.52/0.60    inference(avatar_split_clause,[],[f470,f147,f466,f472])).
% 1.52/0.60  fof(f470,plain,(
% 1.52/0.60    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_funct_1(sK2) | ~spl6_5),
% 1.52/0.60    inference(subsumption_resolution,[],[f459,f149])).
% 1.52/0.60  fof(f459,plain,(
% 1.52/0.60    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.52/0.60    inference(superposition,[],[f80,f196])).
% 1.52/0.60  fof(f80,plain,(
% 1.52/0.60    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f32])).
% 1.52/0.60  fof(f32,plain,(
% 1.52/0.60    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(flattening,[],[f31])).
% 1.52/0.60  fof(f31,plain,(
% 1.52/0.60    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(ennf_transformation,[],[f6])).
% 1.52/0.60  fof(f6,axiom,(
% 1.52/0.60    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.52/0.60  fof(f469,plain,(
% 1.52/0.60    spl6_17 | ~spl6_18 | ~spl6_5),
% 1.52/0.60    inference(avatar_split_clause,[],[f460,f147,f466,f462])).
% 1.52/0.60  fof(f460,plain,(
% 1.52/0.60    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~spl6_5),
% 1.52/0.60    inference(subsumption_resolution,[],[f458,f149])).
% 1.52/0.60  fof(f458,plain,(
% 1.52/0.60    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.52/0.60    inference(superposition,[],[f82,f196])).
% 1.52/0.60  fof(f82,plain,(
% 1.52/0.60    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f56])).
% 1.52/0.60  fof(f56,plain,(
% 1.52/0.60    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(nnf_transformation,[],[f33])).
% 1.52/0.60  fof(f33,plain,(
% 1.52/0.60    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(ennf_transformation,[],[f7])).
% 1.52/0.60  fof(f7,axiom,(
% 1.52/0.60    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 1.52/0.60  fof(f194,plain,(
% 1.52/0.60    spl6_1),
% 1.52/0.60    inference(avatar_contradiction_clause,[],[f193])).
% 1.52/0.60  fof(f193,plain,(
% 1.52/0.60    $false | spl6_1),
% 1.52/0.60    inference(subsumption_resolution,[],[f192,f169])).
% 1.52/0.60  fof(f192,plain,(
% 1.52/0.60    ~v1_relat_1(sK2) | spl6_1),
% 1.52/0.60    inference(subsumption_resolution,[],[f163,f63])).
% 1.52/0.60  fof(f163,plain,(
% 1.52/0.60    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl6_1),
% 1.52/0.60    inference(resolution,[],[f129,f87])).
% 1.52/0.60  fof(f87,plain,(
% 1.52/0.60    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f37])).
% 1.52/0.60  fof(f37,plain,(
% 1.52/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.60    inference(flattening,[],[f36])).
% 1.52/0.60  fof(f36,plain,(
% 1.52/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.60    inference(ennf_transformation,[],[f11])).
% 1.52/0.60  fof(f11,axiom,(
% 1.52/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.52/0.60  fof(f129,plain,(
% 1.52/0.60    ~v1_funct_1(k2_funct_1(sK2)) | spl6_1),
% 1.52/0.60    inference(avatar_component_clause,[],[f127])).
% 1.52/0.60  fof(f191,plain,(
% 1.52/0.60    spl6_4),
% 1.52/0.60    inference(avatar_contradiction_clause,[],[f190])).
% 1.52/0.60  fof(f190,plain,(
% 1.52/0.60    $false | spl6_4),
% 1.52/0.60    inference(subsumption_resolution,[],[f169,f145])).
% 1.52/0.60  fof(f145,plain,(
% 1.52/0.60    ~v1_relat_1(sK2) | spl6_4),
% 1.52/0.60    inference(avatar_component_clause,[],[f143])).
% 1.52/0.60  fof(f143,plain,(
% 1.52/0.60    spl6_4 <=> v1_relat_1(sK2)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.52/0.60  fof(f150,plain,(
% 1.52/0.60    ~spl6_4 | spl6_5),
% 1.52/0.60    inference(avatar_split_clause,[],[f139,f147,f143])).
% 1.52/0.60  fof(f139,plain,(
% 1.52/0.60    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.52/0.60    inference(resolution,[],[f63,f86])).
% 1.52/0.60  fof(f86,plain,(
% 1.52/0.60    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f37])).
% 1.52/0.60  fof(f138,plain,(
% 1.52/0.60    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 1.52/0.60    inference(avatar_split_clause,[],[f68,f135,f131,f127])).
% 1.52/0.60  fof(f68,plain,(
% 1.52/0.60    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.52/0.60    inference(cnf_transformation,[],[f55])).
% 1.52/0.60  % SZS output end Proof for theBenchmark
% 1.52/0.60  % (5377)------------------------------
% 1.52/0.60  % (5377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.60  % (5377)Termination reason: Refutation
% 1.52/0.60  
% 1.52/0.60  % (5377)Memory used [KB]: 11257
% 1.52/0.60  % (5377)Time elapsed: 0.149 s
% 1.52/0.60  % (5377)------------------------------
% 1.52/0.60  % (5377)------------------------------
% 1.52/0.61  % (5368)Success in time 0.237 s
%------------------------------------------------------------------------------
