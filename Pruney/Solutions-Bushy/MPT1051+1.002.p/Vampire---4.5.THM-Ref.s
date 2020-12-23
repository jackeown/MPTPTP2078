%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1051+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 132 expanded)
%              Number of leaves         :   18 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  226 ( 490 expanded)
%              Number of equality atoms :   33 (  93 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f62,f77,f142,f146,f151,f152,f165,f166])).

fof(f166,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f165,plain,
    ( ~ spl5_6
    | spl5_14
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_15
    | ~ spl5_4
    | spl5_11 ),
    inference(avatar_split_clause,[],[f164,f99,f49,f139,f54,f39,f34,f135,f59])).

fof(f59,plain,
    ( spl5_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f135,plain,
    ( spl5_14
  <=> sK1 = k1_tarski(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f34,plain,
    ( spl5_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f39,plain,
    ( spl5_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f54,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f139,plain,
    ( spl5_15
  <=> r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f49,plain,
    ( spl5_4
  <=> k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f99,plain,
    ( spl5_11
  <=> r1_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f164,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 = k1_tarski(sK4(sK1))
    | ~ v1_funct_1(sK3)
    | ~ spl5_4
    | spl5_11 ),
    inference(forward_demodulation,[],[f158,f51])).

fof(f51,plain,
    ( k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f158,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(k5_partfun1(sK0,sK1,sK3),k5_partfun1(sK0,sK1,sK2))
    | sK1 = k1_tarski(sK4(sK1))
    | ~ v1_funct_1(sK3)
    | spl5_11 ),
    inference(resolution,[],[f101,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_relset_1(X0,X1,X3,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
      | k1_tarski(sK4(X1)) = X1
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | ? [X4] : k1_tarski(X4) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | ? [X4] : k1_tarski(X4) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( ! [X4] : k1_tarski(X4) != X1
              & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) )
           => r1_relset_1(X0,X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_2)).

fof(f101,plain,
    ( ~ r1_relset_1(sK0,sK1,sK2,sK3)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f152,plain,
    ( ~ spl5_11
    | spl5_10
    | ~ spl5_9
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f111,f54,f34,f91,f95,f99])).

fof(f95,plain,
    ( spl5_10
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f91,plain,
    ( spl5_9
  <=> r1_relset_1(sK0,sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f111,plain,
    ( ~ r1_relset_1(sK0,sK1,sK3,sK2)
    | sK2 = sK3
    | ~ r1_relset_1(sK0,sK1,sK2,sK3)
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f84,f80])).

fof(f80,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,X0)
        | ~ r1_relset_1(sK0,sK1,sK2,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f26,f36])).

fof(f36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(X2,X3)
      | ~ r1_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_relset_1)).

fof(f84,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3)
        | ~ r1_relset_1(sK0,sK1,sK3,X0)
        | sK3 = X0 )
    | ~ spl5_5 ),
    inference(resolution,[],[f81,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f81,plain,
    ( ! [X1] :
        ( r1_tarski(sK3,X1)
        | ~ r1_relset_1(sK0,sK1,sK3,X1) )
    | ~ spl5_5 ),
    inference(resolution,[],[f26,f56])).

fof(f56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f151,plain,(
    ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f16,f137])).

fof(f137,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f16,plain,(
    ! [X4] : k1_tarski(X4) != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( ( k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
                & ! [X4] : k1_tarski(X4) != X1 )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
              & ! [X4] : k1_tarski(X4) != X1 )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_2)).

fof(f146,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f29,f141])).

fof(f141,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f29,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f142,plain,
    ( ~ spl5_2
    | spl5_14
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_4
    | spl5_9 ),
    inference(avatar_split_clause,[],[f133,f91,f49,f139,f34,f59,f54,f135,f39])).

fof(f133,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 = k1_tarski(sK4(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | spl5_9 ),
    inference(forward_demodulation,[],[f132,f51])).

fof(f132,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
    | sK1 = k1_tarski(sK4(sK1))
    | ~ v1_funct_1(sK2)
    | spl5_9 ),
    inference(resolution,[],[f24,f93])).

fof(f93,plain,
    ( ~ r1_relset_1(sK0,sK1,sK3,sK2)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f77,plain,
    ( spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f67,f54,f74])).

fof(f74,plain,
    ( spl5_8
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f67,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl5_5 ),
    inference(resolution,[],[f32,f56])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f62,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f14,f59])).

fof(f14,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f15,f54])).

fof(f15,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f17,f49])).

fof(f17,plain,(
    k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f18,f44])).

fof(f44,plain,
    ( spl5_3
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f18,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f20,f34])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
