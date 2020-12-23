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
% DateTime   : Thu Dec  3 13:06:09 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 411 expanded)
%              Number of leaves         :   28 ( 122 expanded)
%              Depth                    :   11
%              Number of atoms          :  521 (1818 expanded)
%              Number of equality atoms :  142 ( 457 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1530,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f129,f147,f153,f189,f193,f201,f205,f229,f245,f323,f329,f382,f532,f557,f668,f674,f790,f991,f1108,f1525])).

fof(f1525,plain,(
    ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f1519])).

fof(f1519,plain,
    ( $false
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f1301,f1362,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1362,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f36,f244])).

fof(f244,plain,
    ( sK2 = sK3
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl6_16
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

fof(f1301,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f37,f244])).

fof(f37,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f1108,plain,
    ( spl6_5
    | ~ spl6_19
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f1103])).

fof(f1103,plain,
    ( $false
    | spl6_5
    | ~ spl6_19
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f805,f990])).

fof(f990,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f988])).

fof(f988,plain,
    ( spl6_24
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f805,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl6_5
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f145,f318])).

fof(f318,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl6_19
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f145,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_5
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f991,plain,
    ( spl6_24
    | ~ spl6_23
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f858,f316,f116,f665,f988])).

fof(f665,plain,
    ( spl6_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f116,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f858,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f857,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f857,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f854,f822])).

fof(f822,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f792,f318])).

fof(f792,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f89,f118])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f89,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f40,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f854,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(resolution,[],[f811,f67])).

fof(f67,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f811,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f571,f318])).

fof(f571,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f39,f118])).

fof(f39,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f790,plain,
    ( ~ spl6_2
    | ~ spl6_18
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f789])).

fof(f789,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_18
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f56,f690,f72])).

fof(f690,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_18
    | ~ spl6_22 ),
    inference(backward_demodulation,[],[f586,f663])).

fof(f663,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f661])).

fof(f661,plain,
    ( spl6_22
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f586,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f454,f314])).

fof(f314,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl6_18
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f454,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f37,f118])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f674,plain,
    ( ~ spl6_2
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f669])).

fof(f669,plain,
    ( $false
    | ~ spl6_2
    | spl6_23 ),
    inference(unit_resulting_resolution,[],[f570,f667])).

fof(f667,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f665])).

fof(f570,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f569,f65])).

fof(f569,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f40,f118])).

fof(f668,plain,
    ( spl6_22
    | spl6_19
    | ~ spl6_23
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f614,f116,f665,f316,f661])).

fof(f614,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f612,f65])).

fof(f612,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_2 ),
    inference(resolution,[],[f571,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f557,plain,
    ( spl6_3
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f552])).

fof(f552,plain,
    ( $false
    | spl6_3
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f443,f531])).

fof(f531,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f529])).

fof(f529,plain,
    ( spl6_21
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f443,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | spl6_3
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f121,f318])).

fof(f121,plain,
    ( sK0 != k1_relat_1(sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_3
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f532,plain,
    ( spl6_21
    | ~ spl6_20
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f493,f316,f116,f320,f529])).

fof(f320,plain,
    ( spl6_20
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f493,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f492,f65])).

fof(f492,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f489,f447])).

fof(f447,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f446,f318])).

fof(f446,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f77,f118])).

fof(f77,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f36,f61])).

fof(f489,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(resolution,[],[f451,f67])).

fof(f451,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f450,f318])).

fof(f450,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f35,f118])).

fof(f35,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f382,plain,
    ( ~ spl6_5
    | ~ spl6_10
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_10
    | spl6_15 ),
    inference(trivial_inequality_removal,[],[f380])).

fof(f380,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK2)) != k1_funct_1(sK2,sK4(sK2,sK2))
    | ~ spl6_5
    | ~ spl6_10
    | spl6_15 ),
    inference(forward_demodulation,[],[f240,f348])).

fof(f348,plain,
    ( sK2 = sK3
    | ~ spl6_5
    | ~ spl6_10
    | spl6_15 ),
    inference(unit_resulting_resolution,[],[f38,f90,f247,f146,f206])).

fof(f206,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK3,X0),sK0)
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | sK3 = X0 )
    | ~ spl6_10 ),
    inference(resolution,[],[f188,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f188,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | sK3 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl6_10
  <=> ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | sK3 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f146,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f247,plain,
    ( ~ m1_subset_1(sK4(sK3,sK2),sK0)
    | spl6_15 ),
    inference(unit_resulting_resolution,[],[f240,f33])).

fof(f33,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f90,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f40,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f240,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl6_15
  <=> k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f329,plain,
    ( ~ spl6_2
    | spl6_20 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl6_2
    | spl6_20 ),
    inference(unit_resulting_resolution,[],[f267,f322])).

fof(f322,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f320])).

fof(f267,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f255,f65])).

fof(f255,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f36,f118])).

fof(f323,plain,
    ( spl6_18
    | spl6_19
    | ~ spl6_20
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f277,f116,f320,f316,f312])).

fof(f277,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f275,f65])).

fof(f275,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_2 ),
    inference(resolution,[],[f254,f69])).

fof(f254,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f35,f118])).

fof(f245,plain,
    ( ~ spl6_12
    | ~ spl6_15
    | spl6_16
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f231,f191,f144,f242,f238,f209])).

fof(f209,plain,
    ( spl6_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f191,plain,
    ( spl6_11
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | sK3 = X0
        | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f231,plain,
    ( sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(trivial_inequality_removal,[],[f230])).

fof(f230,plain,
    ( sK0 != sK0
    | sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f221,f146])).

fof(f221,plain,
    ( sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_11 ),
    inference(resolution,[],[f192,f38])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | sK3 = X0
        | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(X0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f191])).

fof(f229,plain,(
    spl6_12 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f40,f211,f62])).

fof(f211,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f209])).

fof(f205,plain,(
    spl6_9 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f34,f185])).

fof(f185,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl6_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f201,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f36,f181,f62])).

fof(f181,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl6_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f193,plain,
    ( ~ spl6_8
    | spl6_11
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f134,f120,f191,f179])).

fof(f134,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
        | sK3 = X0 )
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f73,f122])).

fof(f122,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0 ) ),
    inference(resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f189,plain,
    ( ~ spl6_8
    | ~ spl6_9
    | spl6_10
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f135,f120,f187,f183,f179])).

fof(f135,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK3)
        | sK3 = X0 )
    | ~ spl6_3 ),
    inference(superposition,[],[f46,f122])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f153,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f40,f142])).

fof(f142,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f147,plain,
    ( ~ spl6_4
    | spl6_2
    | spl6_5 ),
    inference(avatar_split_clause,[],[f99,f144,f116,f140])).

fof(f99,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f76,f89])).

fof(f76,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f39,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f129,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f36,f114])).

fof(f114,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f123,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f87,f120,f116,f112])).

fof(f87,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f75,f77])).

fof(f75,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f35,f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (13339)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (13339)Refutation not found, incomplete strategy% (13339)------------------------------
% 0.21/0.49  % (13339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13347)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (13347)Refutation not found, incomplete strategy% (13347)------------------------------
% 0.21/0.50  % (13347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13347)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13347)Memory used [KB]: 10746
% 0.21/0.50  % (13347)Time elapsed: 0.083 s
% 0.21/0.50  % (13347)------------------------------
% 0.21/0.50  % (13347)------------------------------
% 0.21/0.50  % (13339)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13339)Memory used [KB]: 11001
% 0.21/0.50  % (13339)Time elapsed: 0.081 s
% 0.21/0.50  % (13339)------------------------------
% 0.21/0.50  % (13339)------------------------------
% 0.21/0.51  % (13340)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (13348)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (13348)Refutation not found, incomplete strategy% (13348)------------------------------
% 0.21/0.52  % (13348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13348)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13348)Memory used [KB]: 10746
% 0.21/0.52  % (13348)Time elapsed: 0.112 s
% 0.21/0.52  % (13348)------------------------------
% 0.21/0.52  % (13348)------------------------------
% 0.21/0.52  % (13342)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (13349)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (13343)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (13365)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (13361)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.26/0.53  % (13357)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.26/0.53  % (13360)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.26/0.53  % (13344)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.26/0.53  % (13345)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.26/0.54  % (13336)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.54  % (13358)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.26/0.54  % (13355)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.26/0.54  % (13352)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.26/0.54  % (13367)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.26/0.54  % (13362)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.26/0.54  % (13341)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.26/0.54  % (13337)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.54  % (13351)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.26/0.54  % (13364)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.55  % (13353)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.55  % (13363)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.55  % (13346)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.55  % (13359)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.56  % (13366)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.56  % (13350)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.56  % (13354)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.57  % (13345)Refutation not found, incomplete strategy% (13345)------------------------------
% 1.42/0.57  % (13345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (13439)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.42/0.58  % (13345)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.58  
% 1.42/0.58  % (13345)Memory used [KB]: 10874
% 1.42/0.58  % (13345)Time elapsed: 0.153 s
% 1.42/0.58  % (13345)------------------------------
% 1.42/0.58  % (13345)------------------------------
% 1.42/0.58  % (13441)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.42/0.59  % (13360)Refutation not found, incomplete strategy% (13360)------------------------------
% 1.42/0.59  % (13360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.59  % (13360)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.59  
% 1.42/0.59  % (13360)Memory used [KB]: 11001
% 1.42/0.59  % (13360)Time elapsed: 0.182 s
% 1.42/0.59  % (13360)------------------------------
% 1.42/0.59  % (13360)------------------------------
% 1.42/0.59  % (13341)Refutation found. Thanks to Tanya!
% 1.42/0.59  % SZS status Theorem for theBenchmark
% 1.42/0.59  % SZS output start Proof for theBenchmark
% 1.42/0.59  fof(f1530,plain,(
% 1.42/0.59    $false),
% 1.42/0.59    inference(avatar_sat_refutation,[],[f123,f129,f147,f153,f189,f193,f201,f205,f229,f245,f323,f329,f382,f532,f557,f668,f674,f790,f991,f1108,f1525])).
% 1.42/0.59  fof(f1525,plain,(
% 1.42/0.59    ~spl6_16),
% 1.42/0.59    inference(avatar_contradiction_clause,[],[f1519])).
% 1.42/0.59  fof(f1519,plain,(
% 1.42/0.59    $false | ~spl6_16),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f1301,f1362,f72])).
% 1.42/0.59  fof(f72,plain,(
% 1.42/0.59    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.42/0.59    inference(duplicate_literal_removal,[],[f64])).
% 1.42/0.59  fof(f64,plain,(
% 1.42/0.59    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.42/0.59    inference(equality_resolution,[],[f41])).
% 1.42/0.59  fof(f41,plain,(
% 1.42/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f21])).
% 1.42/0.59  fof(f21,plain,(
% 1.42/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.59    inference(flattening,[],[f20])).
% 1.42/0.59  fof(f20,plain,(
% 1.42/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.42/0.59    inference(ennf_transformation,[],[f14])).
% 1.42/0.59  fof(f14,axiom,(
% 1.42/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.42/0.59  fof(f1362,plain,(
% 1.42/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_16),
% 1.42/0.59    inference(forward_demodulation,[],[f36,f244])).
% 1.42/0.59  fof(f244,plain,(
% 1.42/0.59    sK2 = sK3 | ~spl6_16),
% 1.42/0.59    inference(avatar_component_clause,[],[f242])).
% 1.42/0.59  fof(f242,plain,(
% 1.42/0.59    spl6_16 <=> sK2 = sK3),
% 1.42/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.42/0.59  fof(f36,plain,(
% 1.42/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.59    inference(cnf_transformation,[],[f19])).
% 1.42/0.59  fof(f19,plain,(
% 1.42/0.59    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.42/0.59    inference(flattening,[],[f18])).
% 1.42/0.59  fof(f18,plain,(
% 1.42/0.59    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.42/0.59    inference(ennf_transformation,[],[f17])).
% 1.42/0.59  fof(f17,negated_conjecture,(
% 1.42/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.42/0.59    inference(negated_conjecture,[],[f16])).
% 1.42/0.59  fof(f16,conjecture,(
% 1.42/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).
% 1.42/0.59  fof(f1301,plain,(
% 1.42/0.59    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl6_16),
% 1.42/0.59    inference(forward_demodulation,[],[f37,f244])).
% 1.42/0.59  fof(f37,plain,(
% 1.42/0.59    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.42/0.59    inference(cnf_transformation,[],[f19])).
% 1.42/0.59  fof(f1108,plain,(
% 1.42/0.59    spl6_5 | ~spl6_19 | ~spl6_24),
% 1.42/0.59    inference(avatar_contradiction_clause,[],[f1103])).
% 1.42/0.59  fof(f1103,plain,(
% 1.42/0.59    $false | (spl6_5 | ~spl6_19 | ~spl6_24)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f805,f990])).
% 1.42/0.59  fof(f990,plain,(
% 1.42/0.59    k1_xboole_0 = k1_relat_1(sK2) | ~spl6_24),
% 1.42/0.59    inference(avatar_component_clause,[],[f988])).
% 1.42/0.59  fof(f988,plain,(
% 1.42/0.59    spl6_24 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 1.42/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.42/0.59  fof(f805,plain,(
% 1.42/0.59    k1_xboole_0 != k1_relat_1(sK2) | (spl6_5 | ~spl6_19)),
% 1.42/0.59    inference(backward_demodulation,[],[f145,f318])).
% 1.42/0.59  fof(f318,plain,(
% 1.42/0.59    k1_xboole_0 = sK0 | ~spl6_19),
% 1.42/0.59    inference(avatar_component_clause,[],[f316])).
% 1.42/0.59  fof(f316,plain,(
% 1.42/0.59    spl6_19 <=> k1_xboole_0 = sK0),
% 1.42/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.42/0.59  fof(f145,plain,(
% 1.42/0.59    sK0 != k1_relat_1(sK2) | spl6_5),
% 1.42/0.59    inference(avatar_component_clause,[],[f144])).
% 1.42/0.59  fof(f144,plain,(
% 1.42/0.59    spl6_5 <=> sK0 = k1_relat_1(sK2)),
% 1.42/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.42/0.59  fof(f991,plain,(
% 1.42/0.59    spl6_24 | ~spl6_23 | ~spl6_2 | ~spl6_19),
% 1.42/0.59    inference(avatar_split_clause,[],[f858,f316,f116,f665,f988])).
% 1.42/0.59  fof(f665,plain,(
% 1.42/0.59    spl6_23 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.42/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.42/0.59  fof(f116,plain,(
% 1.42/0.59    spl6_2 <=> k1_xboole_0 = sK1),
% 1.42/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.42/0.59  fof(f858,plain,(
% 1.42/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2) | (~spl6_2 | ~spl6_19)),
% 1.42/0.59    inference(forward_demodulation,[],[f857,f65])).
% 1.42/0.59  fof(f65,plain,(
% 1.42/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.42/0.59    inference(equality_resolution,[],[f45])).
% 1.42/0.59  fof(f45,plain,(
% 1.42/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f5])).
% 1.42/0.59  fof(f5,axiom,(
% 1.42/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.42/0.59  fof(f857,plain,(
% 1.42/0.59    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_2 | ~spl6_19)),
% 1.42/0.59    inference(forward_demodulation,[],[f854,f822])).
% 1.42/0.59  fof(f822,plain,(
% 1.42/0.59    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl6_2 | ~spl6_19)),
% 1.42/0.59    inference(backward_demodulation,[],[f792,f318])).
% 1.42/0.59  fof(f792,plain,(
% 1.42/0.59    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) | ~spl6_2),
% 1.42/0.59    inference(forward_demodulation,[],[f89,f118])).
% 1.42/0.59  fof(f118,plain,(
% 1.42/0.59    k1_xboole_0 = sK1 | ~spl6_2),
% 1.42/0.59    inference(avatar_component_clause,[],[f116])).
% 1.42/0.59  fof(f89,plain,(
% 1.42/0.59    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.42/0.59    inference(unit_resulting_resolution,[],[f40,f61])).
% 1.42/0.60  fof(f61,plain,(
% 1.42/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f30])).
% 1.42/0.60  fof(f30,plain,(
% 1.42/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.60    inference(ennf_transformation,[],[f13])).
% 1.42/0.60  fof(f13,axiom,(
% 1.42/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.42/0.60  fof(f40,plain,(
% 1.42/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.60    inference(cnf_transformation,[],[f19])).
% 1.42/0.60  fof(f854,plain,(
% 1.42/0.60    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_2 | ~spl6_19)),
% 1.42/0.60    inference(resolution,[],[f811,f67])).
% 1.42/0.60  fof(f67,plain,(
% 1.42/0.60    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.42/0.60    inference(equality_resolution,[],[f53])).
% 1.42/0.60  fof(f53,plain,(
% 1.42/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f28])).
% 1.42/0.60  fof(f28,plain,(
% 1.42/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.60    inference(flattening,[],[f27])).
% 1.42/0.60  fof(f27,plain,(
% 1.42/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.60    inference(ennf_transformation,[],[f15])).
% 1.42/0.60  fof(f15,axiom,(
% 1.42/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.42/0.60  fof(f811,plain,(
% 1.42/0.60    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl6_2 | ~spl6_19)),
% 1.42/0.60    inference(backward_demodulation,[],[f571,f318])).
% 1.42/0.60  fof(f571,plain,(
% 1.42/0.60    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl6_2),
% 1.42/0.60    inference(forward_demodulation,[],[f39,f118])).
% 1.42/0.60  fof(f39,plain,(
% 1.42/0.60    v1_funct_2(sK2,sK0,sK1)),
% 1.42/0.60    inference(cnf_transformation,[],[f19])).
% 1.42/0.60  fof(f790,plain,(
% 1.42/0.60    ~spl6_2 | ~spl6_18 | ~spl6_22),
% 1.42/0.60    inference(avatar_contradiction_clause,[],[f789])).
% 1.42/0.60  fof(f789,plain,(
% 1.42/0.60    $false | (~spl6_2 | ~spl6_18 | ~spl6_22)),
% 1.42/0.60    inference(unit_resulting_resolution,[],[f56,f690,f72])).
% 1.42/0.60  fof(f690,plain,(
% 1.42/0.60    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_2 | ~spl6_18 | ~spl6_22)),
% 1.42/0.60    inference(backward_demodulation,[],[f586,f663])).
% 1.42/0.60  fof(f663,plain,(
% 1.42/0.60    k1_xboole_0 = sK2 | ~spl6_22),
% 1.42/0.60    inference(avatar_component_clause,[],[f661])).
% 1.42/0.60  fof(f661,plain,(
% 1.42/0.60    spl6_22 <=> k1_xboole_0 = sK2),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.42/0.60  fof(f586,plain,(
% 1.42/0.60    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) | (~spl6_2 | ~spl6_18)),
% 1.42/0.60    inference(backward_demodulation,[],[f454,f314])).
% 1.42/0.60  fof(f314,plain,(
% 1.42/0.60    k1_xboole_0 = sK3 | ~spl6_18),
% 1.42/0.60    inference(avatar_component_clause,[],[f312])).
% 1.42/0.60  fof(f312,plain,(
% 1.42/0.60    spl6_18 <=> k1_xboole_0 = sK3),
% 1.42/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.42/0.61  fof(f454,plain,(
% 1.42/0.61    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3) | ~spl6_2),
% 1.42/0.61    inference(forward_demodulation,[],[f37,f118])).
% 1.42/0.61  fof(f56,plain,(
% 1.42/0.61    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.42/0.61    inference(cnf_transformation,[],[f6])).
% 1.42/0.61  fof(f6,axiom,(
% 1.42/0.61    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.42/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.42/0.61  fof(f674,plain,(
% 1.42/0.61    ~spl6_2 | spl6_23),
% 1.42/0.61    inference(avatar_contradiction_clause,[],[f669])).
% 1.42/0.61  fof(f669,plain,(
% 1.42/0.61    $false | (~spl6_2 | spl6_23)),
% 1.42/0.61    inference(unit_resulting_resolution,[],[f570,f667])).
% 1.42/0.61  fof(f667,plain,(
% 1.42/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl6_23),
% 1.42/0.61    inference(avatar_component_clause,[],[f665])).
% 1.42/0.61  fof(f570,plain,(
% 1.42/0.61    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_2),
% 1.42/0.61    inference(forward_demodulation,[],[f569,f65])).
% 1.42/0.61  fof(f569,plain,(
% 1.42/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_2),
% 1.42/0.61    inference(forward_demodulation,[],[f40,f118])).
% 1.42/0.61  fof(f668,plain,(
% 1.42/0.61    spl6_22 | spl6_19 | ~spl6_23 | ~spl6_2),
% 1.42/0.61    inference(avatar_split_clause,[],[f614,f116,f665,f316,f661])).
% 1.42/0.61  fof(f614,plain,(
% 1.42/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl6_2),
% 1.42/0.61    inference(forward_demodulation,[],[f612,f65])).
% 1.42/0.61  fof(f612,plain,(
% 1.42/0.61    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_2),
% 1.42/0.61    inference(resolution,[],[f571,f69])).
% 1.42/0.61  fof(f69,plain,(
% 1.42/0.61    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.42/0.61    inference(equality_resolution,[],[f51])).
% 1.42/0.61  fof(f51,plain,(
% 1.42/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.42/0.61    inference(cnf_transformation,[],[f28])).
% 1.42/0.61  fof(f557,plain,(
% 1.42/0.61    spl6_3 | ~spl6_19 | ~spl6_21),
% 1.42/0.61    inference(avatar_contradiction_clause,[],[f552])).
% 1.42/0.61  fof(f552,plain,(
% 1.42/0.61    $false | (spl6_3 | ~spl6_19 | ~spl6_21)),
% 1.42/0.61    inference(unit_resulting_resolution,[],[f443,f531])).
% 1.42/0.61  fof(f531,plain,(
% 1.42/0.61    k1_xboole_0 = k1_relat_1(sK3) | ~spl6_21),
% 1.42/0.61    inference(avatar_component_clause,[],[f529])).
% 1.42/0.61  fof(f529,plain,(
% 1.42/0.61    spl6_21 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.42/0.61  fof(f443,plain,(
% 1.42/0.61    k1_xboole_0 != k1_relat_1(sK3) | (spl6_3 | ~spl6_19)),
% 1.42/0.61    inference(forward_demodulation,[],[f121,f318])).
% 1.42/0.61  fof(f121,plain,(
% 1.42/0.61    sK0 != k1_relat_1(sK3) | spl6_3),
% 1.42/0.61    inference(avatar_component_clause,[],[f120])).
% 1.42/0.61  fof(f120,plain,(
% 1.42/0.61    spl6_3 <=> sK0 = k1_relat_1(sK3)),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.42/0.61  fof(f532,plain,(
% 1.42/0.61    spl6_21 | ~spl6_20 | ~spl6_2 | ~spl6_19),
% 1.42/0.61    inference(avatar_split_clause,[],[f493,f316,f116,f320,f529])).
% 1.42/0.61  fof(f320,plain,(
% 1.42/0.61    spl6_20 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.42/0.61  fof(f493,plain,(
% 1.42/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK3) | (~spl6_2 | ~spl6_19)),
% 1.42/0.61    inference(forward_demodulation,[],[f492,f65])).
% 1.42/0.61  fof(f492,plain,(
% 1.42/0.61    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_2 | ~spl6_19)),
% 1.42/0.61    inference(forward_demodulation,[],[f489,f447])).
% 1.42/0.61  fof(f447,plain,(
% 1.42/0.61    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl6_2 | ~spl6_19)),
% 1.42/0.61    inference(forward_demodulation,[],[f446,f318])).
% 1.42/0.61  fof(f446,plain,(
% 1.42/0.61    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl6_2),
% 1.42/0.61    inference(forward_demodulation,[],[f77,f118])).
% 1.42/0.61  fof(f77,plain,(
% 1.42/0.61    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.42/0.61    inference(unit_resulting_resolution,[],[f36,f61])).
% 1.42/0.61  fof(f489,plain,(
% 1.42/0.61    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_2 | ~spl6_19)),
% 1.42/0.61    inference(resolution,[],[f451,f67])).
% 1.42/0.61  fof(f451,plain,(
% 1.42/0.61    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl6_2 | ~spl6_19)),
% 1.42/0.61    inference(forward_demodulation,[],[f450,f318])).
% 1.42/0.61  fof(f450,plain,(
% 1.42/0.61    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl6_2),
% 1.42/0.61    inference(forward_demodulation,[],[f35,f118])).
% 1.42/0.61  fof(f35,plain,(
% 1.42/0.61    v1_funct_2(sK3,sK0,sK1)),
% 1.42/0.61    inference(cnf_transformation,[],[f19])).
% 1.42/0.61  fof(f382,plain,(
% 1.42/0.61    ~spl6_5 | ~spl6_10 | spl6_15),
% 1.42/0.61    inference(avatar_contradiction_clause,[],[f381])).
% 1.42/0.61  fof(f381,plain,(
% 1.42/0.61    $false | (~spl6_5 | ~spl6_10 | spl6_15)),
% 1.42/0.61    inference(trivial_inequality_removal,[],[f380])).
% 1.42/0.61  fof(f380,plain,(
% 1.42/0.61    k1_funct_1(sK2,sK4(sK2,sK2)) != k1_funct_1(sK2,sK4(sK2,sK2)) | (~spl6_5 | ~spl6_10 | spl6_15)),
% 1.42/0.61    inference(forward_demodulation,[],[f240,f348])).
% 1.42/0.61  fof(f348,plain,(
% 1.42/0.61    sK2 = sK3 | (~spl6_5 | ~spl6_10 | spl6_15)),
% 1.42/0.61    inference(unit_resulting_resolution,[],[f38,f90,f247,f146,f206])).
% 1.42/0.61  fof(f206,plain,(
% 1.42/0.61    ( ! [X0] : (m1_subset_1(sK4(sK3,X0),sK0) | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK3 = X0) ) | ~spl6_10),
% 1.42/0.61    inference(resolution,[],[f188,f49])).
% 1.42/0.61  fof(f49,plain,(
% 1.42/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.42/0.61    inference(cnf_transformation,[],[f26])).
% 1.42/0.61  fof(f26,plain,(
% 1.42/0.61    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.42/0.61    inference(ennf_transformation,[],[f7])).
% 1.42/0.61  fof(f7,axiom,(
% 1.42/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.42/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.42/0.61  fof(f188,plain,(
% 1.42/0.61    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl6_10),
% 1.42/0.61    inference(avatar_component_clause,[],[f187])).
% 1.42/0.61  fof(f187,plain,(
% 1.42/0.61    spl6_10 <=> ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.42/0.61  fof(f146,plain,(
% 1.42/0.61    sK0 = k1_relat_1(sK2) | ~spl6_5),
% 1.42/0.61    inference(avatar_component_clause,[],[f144])).
% 1.42/0.61  fof(f247,plain,(
% 1.42/0.61    ~m1_subset_1(sK4(sK3,sK2),sK0) | spl6_15),
% 1.42/0.61    inference(unit_resulting_resolution,[],[f240,f33])).
% 1.42/0.61  fof(f33,plain,(
% 1.42/0.61    ( ! [X4] : (~m1_subset_1(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.42/0.61    inference(cnf_transformation,[],[f19])).
% 1.42/0.61  fof(f90,plain,(
% 1.42/0.61    v1_relat_1(sK2)),
% 1.42/0.61    inference(unit_resulting_resolution,[],[f40,f62])).
% 1.42/0.61  fof(f62,plain,(
% 1.42/0.61    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.61    inference(cnf_transformation,[],[f31])).
% 1.42/0.61  fof(f31,plain,(
% 1.42/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.61    inference(ennf_transformation,[],[f11])).
% 1.42/0.61  fof(f11,axiom,(
% 1.42/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.42/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.42/0.61  fof(f38,plain,(
% 1.42/0.61    v1_funct_1(sK2)),
% 1.42/0.61    inference(cnf_transformation,[],[f19])).
% 1.42/0.61  fof(f240,plain,(
% 1.42/0.61    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | spl6_15),
% 1.42/0.61    inference(avatar_component_clause,[],[f238])).
% 1.42/0.61  fof(f238,plain,(
% 1.42/0.61    spl6_15 <=> k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.42/0.61  fof(f329,plain,(
% 1.42/0.61    ~spl6_2 | spl6_20),
% 1.42/0.61    inference(avatar_contradiction_clause,[],[f324])).
% 1.42/0.61  fof(f324,plain,(
% 1.42/0.61    $false | (~spl6_2 | spl6_20)),
% 1.42/0.61    inference(unit_resulting_resolution,[],[f267,f322])).
% 1.42/0.61  fof(f322,plain,(
% 1.42/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl6_20),
% 1.42/0.61    inference(avatar_component_clause,[],[f320])).
% 1.42/0.61  fof(f267,plain,(
% 1.42/0.61    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_2),
% 1.42/0.61    inference(forward_demodulation,[],[f255,f65])).
% 1.42/0.61  fof(f255,plain,(
% 1.42/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_2),
% 1.42/0.61    inference(backward_demodulation,[],[f36,f118])).
% 1.42/0.61  fof(f323,plain,(
% 1.42/0.61    spl6_18 | spl6_19 | ~spl6_20 | ~spl6_2),
% 1.42/0.61    inference(avatar_split_clause,[],[f277,f116,f320,f316,f312])).
% 1.42/0.61  fof(f277,plain,(
% 1.42/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl6_2),
% 1.42/0.61    inference(forward_demodulation,[],[f275,f65])).
% 1.42/0.61  fof(f275,plain,(
% 1.42/0.61    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_2),
% 1.42/0.61    inference(resolution,[],[f254,f69])).
% 1.42/0.61  fof(f254,plain,(
% 1.42/0.61    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl6_2),
% 1.42/0.61    inference(backward_demodulation,[],[f35,f118])).
% 1.42/0.61  fof(f245,plain,(
% 1.42/0.61    ~spl6_12 | ~spl6_15 | spl6_16 | ~spl6_5 | ~spl6_11),
% 1.42/0.61    inference(avatar_split_clause,[],[f231,f191,f144,f242,f238,f209])).
% 1.42/0.61  fof(f209,plain,(
% 1.42/0.61    spl6_12 <=> v1_relat_1(sK2)),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.42/0.61  fof(f191,plain,(
% 1.42/0.61    spl6_11 <=> ! [X0] : (k1_relat_1(X0) != sK0 | sK3 = X0 | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.42/0.61  fof(f231,plain,(
% 1.42/0.61    sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | ~v1_relat_1(sK2) | (~spl6_5 | ~spl6_11)),
% 1.42/0.61    inference(trivial_inequality_removal,[],[f230])).
% 1.42/0.61  fof(f230,plain,(
% 1.42/0.61    sK0 != sK0 | sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | ~v1_relat_1(sK2) | (~spl6_5 | ~spl6_11)),
% 1.42/0.61    inference(forward_demodulation,[],[f221,f146])).
% 1.42/0.61  fof(f221,plain,(
% 1.42/0.61    sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl6_11),
% 1.42/0.61    inference(resolution,[],[f192,f38])).
% 1.42/0.61  fof(f192,plain,(
% 1.42/0.61    ( ! [X0] : (~v1_funct_1(X0) | sK3 = X0 | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | k1_relat_1(X0) != sK0 | ~v1_relat_1(X0)) ) | ~spl6_11),
% 1.42/0.61    inference(avatar_component_clause,[],[f191])).
% 1.42/0.61  fof(f229,plain,(
% 1.42/0.61    spl6_12),
% 1.42/0.61    inference(avatar_contradiction_clause,[],[f224])).
% 1.42/0.61  fof(f224,plain,(
% 1.42/0.61    $false | spl6_12),
% 1.42/0.61    inference(unit_resulting_resolution,[],[f40,f211,f62])).
% 1.42/0.61  fof(f211,plain,(
% 1.42/0.61    ~v1_relat_1(sK2) | spl6_12),
% 1.42/0.61    inference(avatar_component_clause,[],[f209])).
% 1.42/0.61  fof(f205,plain,(
% 1.42/0.61    spl6_9),
% 1.42/0.61    inference(avatar_contradiction_clause,[],[f202])).
% 1.42/0.61  fof(f202,plain,(
% 1.42/0.61    $false | spl6_9),
% 1.42/0.61    inference(unit_resulting_resolution,[],[f34,f185])).
% 1.42/0.61  fof(f185,plain,(
% 1.42/0.61    ~v1_funct_1(sK3) | spl6_9),
% 1.42/0.61    inference(avatar_component_clause,[],[f183])).
% 1.42/0.61  fof(f183,plain,(
% 1.42/0.61    spl6_9 <=> v1_funct_1(sK3)),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.42/0.61  fof(f34,plain,(
% 1.42/0.61    v1_funct_1(sK3)),
% 1.42/0.61    inference(cnf_transformation,[],[f19])).
% 1.42/0.61  fof(f201,plain,(
% 1.42/0.61    spl6_8),
% 1.42/0.61    inference(avatar_contradiction_clause,[],[f196])).
% 1.42/0.61  fof(f196,plain,(
% 1.42/0.61    $false | spl6_8),
% 1.42/0.61    inference(unit_resulting_resolution,[],[f36,f181,f62])).
% 1.42/0.61  fof(f181,plain,(
% 1.42/0.61    ~v1_relat_1(sK3) | spl6_8),
% 1.42/0.61    inference(avatar_component_clause,[],[f179])).
% 1.42/0.61  fof(f179,plain,(
% 1.42/0.61    spl6_8 <=> v1_relat_1(sK3)),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.42/0.61  fof(f193,plain,(
% 1.42/0.61    ~spl6_8 | spl6_11 | ~spl6_3),
% 1.42/0.61    inference(avatar_split_clause,[],[f134,f120,f191,f179])).
% 1.42/0.61  fof(f134,plain,(
% 1.42/0.61    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0) ) | ~spl6_3),
% 1.42/0.61    inference(backward_demodulation,[],[f73,f122])).
% 1.42/0.61  fof(f122,plain,(
% 1.42/0.61    sK0 = k1_relat_1(sK3) | ~spl6_3),
% 1.42/0.61    inference(avatar_component_clause,[],[f120])).
% 1.42/0.61  fof(f73,plain,(
% 1.42/0.61    ( ! [X0] : (~v1_relat_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0) )),
% 1.42/0.61    inference(resolution,[],[f34,f47])).
% 1.42/0.61  fof(f47,plain,(
% 1.42/0.61    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 1.42/0.61    inference(cnf_transformation,[],[f23])).
% 1.42/0.61  fof(f23,plain,(
% 1.42/0.61    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/0.61    inference(flattening,[],[f22])).
% 1.42/0.61  fof(f22,plain,(
% 1.42/0.61    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.42/0.61    inference(ennf_transformation,[],[f10])).
% 1.42/0.61  fof(f10,axiom,(
% 1.42/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.42/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.42/0.61  fof(f189,plain,(
% 1.42/0.61    ~spl6_8 | ~spl6_9 | spl6_10 | ~spl6_3),
% 1.42/0.61    inference(avatar_split_clause,[],[f135,f120,f187,f183,f179])).
% 1.42/0.61  fof(f135,plain,(
% 1.42/0.61    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | sK3 = X0) ) | ~spl6_3),
% 1.42/0.61    inference(superposition,[],[f46,f122])).
% 1.42/0.61  fof(f46,plain,(
% 1.42/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 1.42/0.61    inference(cnf_transformation,[],[f23])).
% 1.42/0.61  fof(f153,plain,(
% 1.42/0.61    spl6_4),
% 1.42/0.61    inference(avatar_contradiction_clause,[],[f148])).
% 1.42/0.61  fof(f148,plain,(
% 1.42/0.61    $false | spl6_4),
% 1.42/0.61    inference(unit_resulting_resolution,[],[f40,f142])).
% 1.42/0.61  fof(f142,plain,(
% 1.42/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_4),
% 1.42/0.61    inference(avatar_component_clause,[],[f140])).
% 1.42/0.61  fof(f140,plain,(
% 1.42/0.61    spl6_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.42/0.61  fof(f147,plain,(
% 1.42/0.61    ~spl6_4 | spl6_2 | spl6_5),
% 1.42/0.61    inference(avatar_split_clause,[],[f99,f144,f116,f140])).
% 1.42/0.61  fof(f99,plain,(
% 1.42/0.61    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.61    inference(backward_demodulation,[],[f76,f89])).
% 1.42/0.61  fof(f76,plain,(
% 1.42/0.61    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.61    inference(resolution,[],[f39,f55])).
% 1.42/0.61  fof(f55,plain,(
% 1.42/0.61    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.61    inference(cnf_transformation,[],[f28])).
% 1.42/0.61  fof(f129,plain,(
% 1.42/0.61    spl6_1),
% 1.42/0.61    inference(avatar_contradiction_clause,[],[f124])).
% 1.42/0.61  fof(f124,plain,(
% 1.42/0.61    $false | spl6_1),
% 1.42/0.61    inference(unit_resulting_resolution,[],[f36,f114])).
% 1.42/0.61  fof(f114,plain,(
% 1.42/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_1),
% 1.42/0.61    inference(avatar_component_clause,[],[f112])).
% 1.42/0.61  fof(f112,plain,(
% 1.42/0.61    spl6_1 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.42/0.61  fof(f123,plain,(
% 1.42/0.61    ~spl6_1 | spl6_2 | spl6_3),
% 1.42/0.61    inference(avatar_split_clause,[],[f87,f120,f116,f112])).
% 1.42/0.61  fof(f87,plain,(
% 1.42/0.61    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.61    inference(backward_demodulation,[],[f75,f77])).
% 1.42/0.61  fof(f75,plain,(
% 1.42/0.61    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.61    inference(resolution,[],[f35,f55])).
% 1.42/0.61  % SZS output end Proof for theBenchmark
% 1.42/0.61  % (13341)------------------------------
% 1.42/0.61  % (13341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.61  % (13341)Termination reason: Refutation
% 1.42/0.61  
% 1.42/0.61  % (13341)Memory used [KB]: 6780
% 1.42/0.61  % (13341)Time elapsed: 0.188 s
% 1.42/0.61  % (13341)------------------------------
% 1.42/0.61  % (13341)------------------------------
% 1.42/0.61  % (13333)Success in time 0.244 s
%------------------------------------------------------------------------------
