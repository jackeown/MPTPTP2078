%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:12 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 613 expanded)
%              Number of leaves         :   26 ( 159 expanded)
%              Depth                    :   17
%              Number of atoms          :  566 (2829 expanded)
%              Number of equality atoms :  133 ( 700 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f610,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f136,f177,f309,f446,f469,f485,f508,f578,f609])).

fof(f609,plain,
    ( spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f607,f408])).

fof(f408,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f407,f222])).

fof(f222,plain,(
    ! [X4,X3] : sP0(X3,k1_xboole_0,X4) ),
    inference(resolution,[],[f90,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f35,f38])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f407,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ sP0(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(trivial_inequality_removal,[],[f406])).

fof(f406,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ sP0(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f100,f360])).

fof(f360,plain,(
    ! [X4,X5] : k1_xboole_0 = k1_relset_1(X4,X5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f355,f183])).

fof(f183,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f95,f168])).

fof(f168,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f165,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f165,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f75,f125])).

fof(f125,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f76,f118])).

fof(f118,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f61,f98])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f95,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f62,f59])).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f62,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f355,plain,(
    ! [X4,X5] : k1_relat_1(k1_xboole_0) = k1_relset_1(X4,X5,k1_xboole_0) ),
    inference(resolution,[],[f83,f58])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f100,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1)
      | v1_funct_2(X1,k1_xboole_0,X2)
      | ~ sP0(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f607,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f585,f593])).

fof(f593,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(resolution,[],[f590,f162])).

fof(f162,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f75,f57])).

fof(f590,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(resolution,[],[f583,f76])).

fof(f583,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f582,f513])).

fof(f513,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f512,f98])).

fof(f512,plain,
    ( sK3 = k2_zfmisc_1(sK1,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f176,f445])).

fof(f445,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f443])).

fof(f443,plain,
    ( spl4_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f176,plain,
    ( sK3 = k2_zfmisc_1(sK1,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_5
  <=> sK3 = k2_zfmisc_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f582,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f581,f99])).

fof(f99,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f581,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_3
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f115,f445])).

fof(f115,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_3
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f585,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f584,f513])).

fof(f584,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f112,f445])).

fof(f112,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_2
  <=> v1_funct_2(k2_funct_1(sK3),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f578,plain,
    ( ~ spl4_1
    | spl4_3
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | ~ spl4_1
    | spl4_3
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f576,f561])).

fof(f561,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f504,f513])).

fof(f504,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f492,f99])).

fof(f492,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | spl4_3
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f116,f445])).

fof(f116,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f576,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f575,f98])).

fof(f575,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f574,f541])).

fof(f541,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f280,f513])).

fof(f280,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl4_8
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f574,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f572,f538])).

fof(f538,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f107,f513])).

fof(f107,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_1
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f572,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(superposition,[],[f66,f552])).

fof(f552,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f551,f183])).

fof(f551,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f550,f130])).

fof(f130,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f81,f58])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f550,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f548,f536])).

fof(f536,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f51,f513])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f548,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(resolution,[],[f537,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f537,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f54,f513])).

fof(f54,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f508,plain,
    ( spl4_4
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f507])).

fof(f507,plain,
    ( $false
    | spl4_4
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f506,f57])).

fof(f506,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl4_4
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f494,f98])).

fof(f494,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK3)
    | spl4_4
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f172,f445])).

fof(f172,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl4_4
  <=> r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f485,plain,
    ( ~ spl4_1
    | spl4_3
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | ~ spl4_1
    | spl4_3
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f483,f116])).

fof(f483,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f482,f333])).

fof(f333,plain,(
    sK2 = k1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f271,f330])).

fof(f330,plain,(
    sK2 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f325,f55])).

fof(f55,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f325,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f82,f53])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f271,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f270,f132])).

fof(f132,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f81,f53])).

fof(f270,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f269,f51])).

fof(f269,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f69,f54])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f482,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),sK1)))
    | ~ spl4_1
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f481,f280])).

fof(f481,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),sK1)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f479,f107])).

fof(f479,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_18 ),
    inference(superposition,[],[f66,f452])).

fof(f452,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f312,f451])).

fof(f451,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f357,f441])).

fof(f441,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl4_18
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f357,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f83,f53])).

fof(f312,plain,(
    k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f311,f132])).

fof(f311,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f310,f51])).

fof(f310,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f70,f54])).

fof(f469,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f453,f112])).

fof(f453,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ spl4_1
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f331,f451])).

fof(f331,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f320,f330])).

fof(f320,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f319,f271])).

fof(f319,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f318,f280])).

fof(f318,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f314,f107])).

fof(f314,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[],[f65,f312])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f446,plain,
    ( spl4_18
    | spl4_19 ),
    inference(avatar_split_clause,[],[f437,f443,f439])).

fof(f437,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f433,f52])).

fof(f52,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f433,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f86,f224])).

fof(f224,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f90,f53])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f309,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f307,f132])).

fof(f307,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_8 ),
    inference(subsumption_resolution,[],[f306,f51])).

fof(f306,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_8 ),
    inference(resolution,[],[f281,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f281,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f279])).

fof(f177,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f166,f174,f170])).

fof(f166,plain,
    ( sK3 = k2_zfmisc_1(sK1,sK2)
    | ~ r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) ),
    inference(resolution,[],[f75,f123])).

fof(f123,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f76,f53])).

fof(f136,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f132,f121])).

fof(f121,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f120,f51])).

fof(f120,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_1 ),
    inference(resolution,[],[f68,f108])).

fof(f108,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f117,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f56,f114,f110,f106])).

fof(f56,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:12:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.51  % (19702)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (19695)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.53  % (19694)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.52/0.56  % (19709)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.52/0.56  % (19702)Refutation found. Thanks to Tanya!
% 1.52/0.56  % SZS status Theorem for theBenchmark
% 1.52/0.56  % (19704)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.52/0.56  % (19727)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.52/0.56  % (19711)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.52/0.57  % (19717)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.52/0.57  % (19707)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.52/0.57  % (19696)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.52/0.57  % (19700)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f610,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(avatar_sat_refutation,[],[f117,f136,f177,f309,f446,f469,f485,f508,f578,f609])).
% 1.52/0.57  fof(f609,plain,(
% 1.52/0.57    spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_19),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f608])).
% 1.52/0.57  fof(f608,plain,(
% 1.52/0.57    $false | (spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(subsumption_resolution,[],[f607,f408])).
% 1.52/0.57  fof(f408,plain,(
% 1.52/0.57    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f407,f222])).
% 1.52/0.57  fof(f222,plain,(
% 1.52/0.57    ( ! [X4,X3] : (sP0(X3,k1_xboole_0,X4)) )),
% 1.52/0.57    inference(resolution,[],[f90,f58])).
% 1.52/0.57  fof(f58,plain,(
% 1.52/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.52/0.57  fof(f90,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f50])).
% 1.52/0.57  fof(f50,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(nnf_transformation,[],[f39])).
% 1.52/0.57  fof(f39,plain,(
% 1.52/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(definition_folding,[],[f35,f38])).
% 1.52/0.57  fof(f38,plain,(
% 1.52/0.57    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.52/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.52/0.57  fof(f35,plain,(
% 1.52/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(flattening,[],[f34])).
% 1.52/0.57  fof(f34,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(ennf_transformation,[],[f15])).
% 1.52/0.57  fof(f15,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.52/0.57  fof(f407,plain,(
% 1.52/0.57    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~sP0(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.52/0.57    inference(trivial_inequality_removal,[],[f406])).
% 1.52/0.57  fof(f406,plain,(
% 1.52/0.57    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~sP0(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.52/0.57    inference(superposition,[],[f100,f360])).
% 1.52/0.57  fof(f360,plain,(
% 1.52/0.57    ( ! [X4,X5] : (k1_xboole_0 = k1_relset_1(X4,X5,k1_xboole_0)) )),
% 1.52/0.57    inference(forward_demodulation,[],[f355,f183])).
% 1.52/0.57  fof(f183,plain,(
% 1.52/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.52/0.57    inference(superposition,[],[f95,f168])).
% 1.52/0.57  fof(f168,plain,(
% 1.52/0.57    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.52/0.57    inference(subsumption_resolution,[],[f165,f57])).
% 1.52/0.57  fof(f57,plain,(
% 1.52/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.52/0.57  fof(f165,plain,(
% 1.52/0.57    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0))),
% 1.52/0.57    inference(resolution,[],[f75,f125])).
% 1.52/0.57  fof(f125,plain,(
% 1.52/0.57    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)),
% 1.52/0.57    inference(resolution,[],[f76,f118])).
% 1.52/0.57  fof(f118,plain,(
% 1.52/0.57    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.52/0.57    inference(superposition,[],[f61,f98])).
% 1.52/0.57  fof(f98,plain,(
% 1.52/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f80])).
% 1.52/0.57  fof(f80,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f47])).
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.52/0.57    inference(flattening,[],[f46])).
% 1.52/0.57  fof(f46,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.52/0.57    inference(nnf_transformation,[],[f3])).
% 1.52/0.57  fof(f3,axiom,(
% 1.52/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.52/0.57  fof(f61,plain,(
% 1.52/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f16,axiom,(
% 1.52/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.52/0.57  fof(f76,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f45])).
% 1.52/0.57  fof(f45,plain,(
% 1.52/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.52/0.57    inference(nnf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.52/0.57  fof(f75,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f44])).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.57    inference(flattening,[],[f43])).
% 1.52/0.57  fof(f43,plain,(
% 1.52/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.57    inference(nnf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.52/0.57  fof(f95,plain,(
% 1.52/0.57    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.52/0.57    inference(definition_unfolding,[],[f62,f59])).
% 1.52/0.57  fof(f59,plain,(
% 1.52/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f17])).
% 1.52/0.57  fof(f17,axiom,(
% 1.52/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.52/0.57  fof(f62,plain,(
% 1.52/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f8])).
% 1.52/0.57  fof(f8,axiom,(
% 1.52/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.52/0.57  fof(f355,plain,(
% 1.52/0.57    ( ! [X4,X5] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X4,X5,k1_xboole_0)) )),
% 1.52/0.57    inference(resolution,[],[f83,f58])).
% 1.52/0.57  fof(f83,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f32,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(ennf_transformation,[],[f13])).
% 1.52/0.57  fof(f13,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.52/0.57  fof(f100,plain,(
% 1.52/0.57    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1) | v1_funct_2(X1,k1_xboole_0,X2) | ~sP0(k1_xboole_0,X1,X2)) )),
% 1.52/0.57    inference(equality_resolution,[],[f89])).
% 1.52/0.57  fof(f89,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f49])).
% 1.52/0.57  fof(f49,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.52/0.57    inference(rectify,[],[f48])).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.52/0.57    inference(nnf_transformation,[],[f38])).
% 1.52/0.57  fof(f607,plain,(
% 1.52/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f585,f593])).
% 1.52/0.57  fof(f593,plain,(
% 1.52/0.57    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl4_3 | ~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(resolution,[],[f590,f162])).
% 1.52/0.57  fof(f162,plain,(
% 1.52/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.52/0.57    inference(resolution,[],[f75,f57])).
% 1.52/0.57  fof(f590,plain,(
% 1.52/0.57    r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) | (~spl4_3 | ~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(resolution,[],[f583,f76])).
% 1.52/0.57  fof(f583,plain,(
% 1.52/0.57    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_3 | ~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f582,f513])).
% 1.52/0.57  fof(f513,plain,(
% 1.52/0.57    k1_xboole_0 = sK3 | (~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f512,f98])).
% 1.52/0.57  fof(f512,plain,(
% 1.52/0.57    sK3 = k2_zfmisc_1(sK1,k1_xboole_0) | (~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f176,f445])).
% 1.52/0.57  fof(f445,plain,(
% 1.52/0.57    k1_xboole_0 = sK2 | ~spl4_19),
% 1.52/0.57    inference(avatar_component_clause,[],[f443])).
% 1.52/0.57  fof(f443,plain,(
% 1.52/0.57    spl4_19 <=> k1_xboole_0 = sK2),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.52/0.57  fof(f176,plain,(
% 1.52/0.57    sK3 = k2_zfmisc_1(sK1,sK2) | ~spl4_5),
% 1.52/0.57    inference(avatar_component_clause,[],[f174])).
% 1.52/0.57  fof(f174,plain,(
% 1.52/0.57    spl4_5 <=> sK3 = k2_zfmisc_1(sK1,sK2)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.52/0.57  fof(f582,plain,(
% 1.52/0.57    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | (~spl4_3 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f581,f99])).
% 1.52/0.57  fof(f99,plain,(
% 1.52/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.52/0.57    inference(equality_resolution,[],[f79])).
% 1.52/0.57  fof(f79,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f47])).
% 1.52/0.57  fof(f581,plain,(
% 1.52/0.57    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl4_3 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f115,f445])).
% 1.52/0.57  fof(f115,plain,(
% 1.52/0.57    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 1.52/0.57    inference(avatar_component_clause,[],[f114])).
% 1.52/0.57  fof(f114,plain,(
% 1.52/0.57    spl4_3 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.52/0.57  fof(f585,plain,(
% 1.52/0.57    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | (spl4_2 | ~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f584,f513])).
% 1.52/0.57  fof(f584,plain,(
% 1.52/0.57    ~v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) | (spl4_2 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f112,f445])).
% 1.52/0.57  fof(f112,plain,(
% 1.52/0.57    ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | spl4_2),
% 1.52/0.57    inference(avatar_component_clause,[],[f110])).
% 1.52/0.57  fof(f110,plain,(
% 1.52/0.57    spl4_2 <=> v1_funct_2(k2_funct_1(sK3),sK2,sK1)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.52/0.57  fof(f578,plain,(
% 1.52/0.57    ~spl4_1 | spl4_3 | ~spl4_5 | ~spl4_8 | ~spl4_19),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f577])).
% 1.52/0.57  fof(f577,plain,(
% 1.52/0.57    $false | (~spl4_1 | spl4_3 | ~spl4_5 | ~spl4_8 | ~spl4_19)),
% 1.52/0.57    inference(subsumption_resolution,[],[f576,f561])).
% 1.52/0.57  fof(f561,plain,(
% 1.52/0.57    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f504,f513])).
% 1.52/0.57  fof(f504,plain,(
% 1.52/0.57    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f492,f99])).
% 1.52/0.57  fof(f492,plain,(
% 1.52/0.57    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (spl4_3 | ~spl4_19)),
% 1.52/0.57    inference(backward_demodulation,[],[f116,f445])).
% 1.52/0.57  fof(f116,plain,(
% 1.52/0.57    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.52/0.57    inference(avatar_component_clause,[],[f114])).
% 1.52/0.57  fof(f576,plain,(
% 1.52/0.57    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_1 | ~spl4_5 | ~spl4_8 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f575,f98])).
% 1.52/0.57  fof(f575,plain,(
% 1.52/0.57    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0))) | (~spl4_1 | ~spl4_5 | ~spl4_8 | ~spl4_19)),
% 1.52/0.57    inference(subsumption_resolution,[],[f574,f541])).
% 1.52/0.57  fof(f541,plain,(
% 1.52/0.57    v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_5 | ~spl4_8 | ~spl4_19)),
% 1.52/0.57    inference(backward_demodulation,[],[f280,f513])).
% 1.52/0.57  fof(f280,plain,(
% 1.52/0.57    v1_relat_1(k2_funct_1(sK3)) | ~spl4_8),
% 1.52/0.57    inference(avatar_component_clause,[],[f279])).
% 1.52/0.57  fof(f279,plain,(
% 1.52/0.57    spl4_8 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.52/0.57  fof(f574,plain,(
% 1.52/0.57    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0))) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_1 | ~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(subsumption_resolution,[],[f572,f538])).
% 1.52/0.57  fof(f538,plain,(
% 1.52/0.57    v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl4_1 | ~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(backward_demodulation,[],[f107,f513])).
% 1.52/0.57  fof(f107,plain,(
% 1.52/0.57    v1_funct_1(k2_funct_1(sK3)) | ~spl4_1),
% 1.52/0.57    inference(avatar_component_clause,[],[f106])).
% 1.52/0.57  fof(f106,plain,(
% 1.52/0.57    spl4_1 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.52/0.57  fof(f572,plain,(
% 1.52/0.57    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0))) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(superposition,[],[f66,f552])).
% 1.52/0.57  fof(f552,plain,(
% 1.52/0.57    k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f551,f183])).
% 1.52/0.57  fof(f551,plain,(
% 1.52/0.57    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(subsumption_resolution,[],[f550,f130])).
% 1.52/0.57  fof(f130,plain,(
% 1.52/0.57    v1_relat_1(k1_xboole_0)),
% 1.52/0.57    inference(resolution,[],[f81,f58])).
% 1.52/0.57  fof(f81,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f30])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(ennf_transformation,[],[f11])).
% 1.52/0.57  fof(f11,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.52/0.57  fof(f550,plain,(
% 1.52/0.57    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | (~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(subsumption_resolution,[],[f548,f536])).
% 1.52/0.57  fof(f536,plain,(
% 1.52/0.57    v1_funct_1(k1_xboole_0) | (~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(backward_demodulation,[],[f51,f513])).
% 1.52/0.57  fof(f51,plain,(
% 1.52/0.57    v1_funct_1(sK3)),
% 1.52/0.57    inference(cnf_transformation,[],[f41])).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f40])).
% 1.52/0.57  fof(f40,plain,(
% 1.52/0.57    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.52/0.57    inference(flattening,[],[f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.52/0.57    inference(ennf_transformation,[],[f20])).
% 1.52/0.57  fof(f20,negated_conjecture,(
% 1.52/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.52/0.57    inference(negated_conjecture,[],[f19])).
% 1.52/0.57  fof(f19,conjecture,(
% 1.52/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.52/0.57  fof(f548,plain,(
% 1.52/0.57    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(resolution,[],[f537,f70])).
% 1.52/0.57  fof(f70,plain,(
% 1.52/0.57    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f28])).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(flattening,[],[f27])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f10])).
% 1.52/0.57  fof(f10,axiom,(
% 1.52/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.52/0.57  fof(f537,plain,(
% 1.52/0.57    v2_funct_1(k1_xboole_0) | (~spl4_5 | ~spl4_19)),
% 1.52/0.57    inference(backward_demodulation,[],[f54,f513])).
% 1.52/0.57  fof(f54,plain,(
% 1.52/0.57    v2_funct_1(sK3)),
% 1.52/0.57    inference(cnf_transformation,[],[f41])).
% 1.52/0.57  fof(f66,plain,(
% 1.52/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f24])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(flattening,[],[f23])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f18])).
% 1.52/0.57  fof(f18,axiom,(
% 1.52/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.52/0.57  fof(f508,plain,(
% 1.52/0.57    spl4_4 | ~spl4_19),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f507])).
% 1.52/0.57  fof(f507,plain,(
% 1.52/0.57    $false | (spl4_4 | ~spl4_19)),
% 1.52/0.57    inference(subsumption_resolution,[],[f506,f57])).
% 1.52/0.57  fof(f506,plain,(
% 1.52/0.57    ~r1_tarski(k1_xboole_0,sK3) | (spl4_4 | ~spl4_19)),
% 1.52/0.57    inference(forward_demodulation,[],[f494,f98])).
% 1.52/0.57  fof(f494,plain,(
% 1.52/0.57    ~r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK3) | (spl4_4 | ~spl4_19)),
% 1.52/0.57    inference(backward_demodulation,[],[f172,f445])).
% 1.52/0.57  fof(f172,plain,(
% 1.52/0.57    ~r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) | spl4_4),
% 1.52/0.57    inference(avatar_component_clause,[],[f170])).
% 1.52/0.57  fof(f170,plain,(
% 1.52/0.57    spl4_4 <=> r1_tarski(k2_zfmisc_1(sK1,sK2),sK3)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.52/0.57  fof(f485,plain,(
% 1.52/0.57    ~spl4_1 | spl4_3 | ~spl4_8 | ~spl4_18),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f484])).
% 1.52/0.57  fof(f484,plain,(
% 1.52/0.57    $false | (~spl4_1 | spl4_3 | ~spl4_8 | ~spl4_18)),
% 1.52/0.57    inference(subsumption_resolution,[],[f483,f116])).
% 1.52/0.57  fof(f483,plain,(
% 1.52/0.57    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_8 | ~spl4_18)),
% 1.52/0.57    inference(forward_demodulation,[],[f482,f333])).
% 1.52/0.57  fof(f333,plain,(
% 1.52/0.57    sK2 = k1_relat_1(k2_funct_1(sK3))),
% 1.52/0.57    inference(backward_demodulation,[],[f271,f330])).
% 1.52/0.57  fof(f330,plain,(
% 1.52/0.57    sK2 = k2_relat_1(sK3)),
% 1.52/0.57    inference(forward_demodulation,[],[f325,f55])).
% 1.52/0.57  fof(f55,plain,(
% 1.52/0.57    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 1.52/0.57    inference(cnf_transformation,[],[f41])).
% 1.52/0.57  fof(f325,plain,(
% 1.52/0.57    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.52/0.57    inference(resolution,[],[f82,f53])).
% 1.52/0.57  fof(f53,plain,(
% 1.52/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.52/0.57    inference(cnf_transformation,[],[f41])).
% 1.52/0.57  fof(f82,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f31])).
% 1.52/0.57  fof(f31,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(ennf_transformation,[],[f14])).
% 1.52/0.57  fof(f14,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.52/0.57  fof(f271,plain,(
% 1.52/0.57    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.52/0.57    inference(subsumption_resolution,[],[f270,f132])).
% 1.52/0.57  fof(f132,plain,(
% 1.52/0.57    v1_relat_1(sK3)),
% 1.52/0.57    inference(resolution,[],[f81,f53])).
% 1.52/0.57  fof(f270,plain,(
% 1.52/0.57    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 1.52/0.57    inference(subsumption_resolution,[],[f269,f51])).
% 1.52/0.57  fof(f269,plain,(
% 1.52/0.57    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.52/0.57    inference(resolution,[],[f69,f54])).
% 1.52/0.57  fof(f69,plain,(
% 1.52/0.57    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f28])).
% 1.52/0.57  fof(f482,plain,(
% 1.52/0.57    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),sK1))) | (~spl4_1 | ~spl4_8 | ~spl4_18)),
% 1.52/0.57    inference(subsumption_resolution,[],[f481,f280])).
% 1.52/0.57  fof(f481,plain,(
% 1.52/0.57    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),sK1))) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_18)),
% 1.52/0.57    inference(subsumption_resolution,[],[f479,f107])).
% 1.52/0.57  fof(f479,plain,(
% 1.52/0.57    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),sK1))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_18),
% 1.52/0.57    inference(superposition,[],[f66,f452])).
% 1.52/0.57  fof(f452,plain,(
% 1.52/0.57    sK1 = k2_relat_1(k2_funct_1(sK3)) | ~spl4_18),
% 1.52/0.57    inference(backward_demodulation,[],[f312,f451])).
% 1.52/0.57  fof(f451,plain,(
% 1.52/0.57    sK1 = k1_relat_1(sK3) | ~spl4_18),
% 1.52/0.57    inference(backward_demodulation,[],[f357,f441])).
% 1.52/0.57  fof(f441,plain,(
% 1.52/0.57    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl4_18),
% 1.52/0.57    inference(avatar_component_clause,[],[f439])).
% 1.52/0.57  fof(f439,plain,(
% 1.52/0.57    spl4_18 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.52/0.57  fof(f357,plain,(
% 1.52/0.57    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 1.52/0.57    inference(resolution,[],[f83,f53])).
% 1.52/0.57  fof(f312,plain,(
% 1.52/0.57    k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)),
% 1.52/0.57    inference(subsumption_resolution,[],[f311,f132])).
% 1.52/0.57  fof(f311,plain,(
% 1.52/0.57    k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.52/0.57    inference(subsumption_resolution,[],[f310,f51])).
% 1.52/0.57  fof(f310,plain,(
% 1.52/0.57    k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.52/0.57    inference(resolution,[],[f70,f54])).
% 1.52/0.57  fof(f469,plain,(
% 1.52/0.57    ~spl4_1 | spl4_2 | ~spl4_8 | ~spl4_18),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f468])).
% 1.52/0.57  fof(f468,plain,(
% 1.52/0.57    $false | (~spl4_1 | spl4_2 | ~spl4_8 | ~spl4_18)),
% 1.52/0.57    inference(subsumption_resolution,[],[f453,f112])).
% 1.52/0.57  fof(f453,plain,(
% 1.52/0.57    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | (~spl4_1 | ~spl4_8 | ~spl4_18)),
% 1.52/0.57    inference(backward_demodulation,[],[f331,f451])).
% 1.52/0.57  fof(f331,plain,(
% 1.52/0.57    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) | (~spl4_1 | ~spl4_8)),
% 1.52/0.57    inference(backward_demodulation,[],[f320,f330])).
% 1.52/0.57  fof(f320,plain,(
% 1.52/0.57    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) | (~spl4_1 | ~spl4_8)),
% 1.52/0.57    inference(forward_demodulation,[],[f319,f271])).
% 1.52/0.57  fof(f319,plain,(
% 1.52/0.57    v1_funct_2(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) | (~spl4_1 | ~spl4_8)),
% 1.52/0.57    inference(subsumption_resolution,[],[f318,f280])).
% 1.52/0.57  fof(f318,plain,(
% 1.52/0.57    v1_funct_2(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_1),
% 1.52/0.57    inference(subsumption_resolution,[],[f314,f107])).
% 1.52/0.57  fof(f314,plain,(
% 1.52/0.57    v1_funct_2(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.52/0.57    inference(superposition,[],[f65,f312])).
% 1.52/0.57  fof(f65,plain,(
% 1.52/0.57    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f24])).
% 1.52/0.57  fof(f446,plain,(
% 1.52/0.57    spl4_18 | spl4_19),
% 1.52/0.57    inference(avatar_split_clause,[],[f437,f443,f439])).
% 1.52/0.57  fof(f437,plain,(
% 1.52/0.57    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.52/0.57    inference(subsumption_resolution,[],[f433,f52])).
% 1.52/0.57  fof(f52,plain,(
% 1.52/0.57    v1_funct_2(sK3,sK1,sK2)),
% 1.52/0.57    inference(cnf_transformation,[],[f41])).
% 1.52/0.57  fof(f433,plain,(
% 1.52/0.57    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.52/0.57    inference(resolution,[],[f86,f224])).
% 1.52/0.57  fof(f224,plain,(
% 1.52/0.57    sP0(sK1,sK3,sK2)),
% 1.52/0.57    inference(resolution,[],[f90,f53])).
% 1.52/0.57  fof(f86,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f49])).
% 1.52/0.57  fof(f309,plain,(
% 1.52/0.57    spl4_8),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f308])).
% 1.52/0.57  fof(f308,plain,(
% 1.52/0.57    $false | spl4_8),
% 1.52/0.57    inference(subsumption_resolution,[],[f307,f132])).
% 1.52/0.57  fof(f307,plain,(
% 1.52/0.57    ~v1_relat_1(sK3) | spl4_8),
% 1.52/0.57    inference(subsumption_resolution,[],[f306,f51])).
% 1.52/0.57  fof(f306,plain,(
% 1.52/0.57    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_8),
% 1.52/0.57    inference(resolution,[],[f281,f67])).
% 1.52/0.57  fof(f67,plain,(
% 1.52/0.57    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  fof(f26,plain,(
% 1.52/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(flattening,[],[f25])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f9])).
% 1.52/0.57  fof(f9,axiom,(
% 1.52/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.52/0.57  fof(f281,plain,(
% 1.52/0.57    ~v1_relat_1(k2_funct_1(sK3)) | spl4_8),
% 1.52/0.57    inference(avatar_component_clause,[],[f279])).
% 1.52/0.57  fof(f177,plain,(
% 1.52/0.57    ~spl4_4 | spl4_5),
% 1.52/0.57    inference(avatar_split_clause,[],[f166,f174,f170])).
% 1.52/0.57  fof(f166,plain,(
% 1.52/0.57    sK3 = k2_zfmisc_1(sK1,sK2) | ~r1_tarski(k2_zfmisc_1(sK1,sK2),sK3)),
% 1.52/0.57    inference(resolution,[],[f75,f123])).
% 1.52/0.57  fof(f123,plain,(
% 1.52/0.57    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 1.52/0.57    inference(resolution,[],[f76,f53])).
% 1.52/0.57  fof(f136,plain,(
% 1.52/0.57    spl4_1),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f135])).
% 1.52/0.57  fof(f135,plain,(
% 1.52/0.57    $false | spl4_1),
% 1.52/0.57    inference(subsumption_resolution,[],[f132,f121])).
% 1.52/0.57  fof(f121,plain,(
% 1.52/0.57    ~v1_relat_1(sK3) | spl4_1),
% 1.52/0.57    inference(subsumption_resolution,[],[f120,f51])).
% 1.52/0.57  fof(f120,plain,(
% 1.52/0.57    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_1),
% 1.52/0.57    inference(resolution,[],[f68,f108])).
% 1.52/0.57  fof(f108,plain,(
% 1.52/0.57    ~v1_funct_1(k2_funct_1(sK3)) | spl4_1),
% 1.52/0.57    inference(avatar_component_clause,[],[f106])).
% 1.52/0.57  fof(f68,plain,(
% 1.52/0.57    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  fof(f117,plain,(
% 1.52/0.57    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.52/0.57    inference(avatar_split_clause,[],[f56,f114,f110,f106])).
% 1.52/0.57  fof(f56,plain,(
% 1.52/0.57    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.52/0.57    inference(cnf_transformation,[],[f41])).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (19702)------------------------------
% 1.52/0.57  % (19702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (19702)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (19702)Memory used [KB]: 11001
% 1.52/0.57  % (19702)Time elapsed: 0.137 s
% 1.52/0.57  % (19702)------------------------------
% 1.52/0.57  % (19702)------------------------------
% 1.52/0.57  % (19692)Success in time 0.223 s
%------------------------------------------------------------------------------
