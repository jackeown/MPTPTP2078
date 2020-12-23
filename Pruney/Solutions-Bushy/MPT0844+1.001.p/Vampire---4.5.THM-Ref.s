%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0844+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 121 expanded)
%              Number of leaves         :   21 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  193 ( 281 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f56,f67,f72,f83,f89,f105,f115,f122,f129,f141])).

fof(f141,plain,
    ( ~ spl4_2
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl4_2
    | spl4_15 ),
    inference(subsumption_resolution,[],[f135,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f135,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl4_15 ),
    inference(resolution,[],[f128,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f128,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_15
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f129,plain,
    ( ~ spl4_15
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f123,f120,f44,f126])).

fof(f44,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f120,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f123,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(resolution,[],[f121,f46])).

fof(f46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_xboole_0(X0,sK1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( spl4_14
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f117,f113,f120])).

fof(f113,plain,
    ( spl4_13
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK1)
        | ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_13 ),
    inference(resolution,[],[f114,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f114,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0))
        | ~ r1_xboole_0(X0,sK1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl4_13
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f111,f87,f113])).

fof(f87,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK1)
        | ~ r1_tarski(k1_relat_1(sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK1)
        | ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0)) )
    | ~ spl4_10 ),
    inference(resolution,[],[f88,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK3),X0)
        | ~ r1_xboole_0(X0,sK1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f105,plain,
    ( ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f71,f46])).

fof(f71,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_7
  <=> ! [X1,X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f89,plain,
    ( spl4_10
    | spl4_9 ),
    inference(avatar_split_clause,[],[f84,f80,f87])).

fof(f80,plain,
    ( spl4_9
  <=> r1_xboole_0(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK1)
        | ~ r1_tarski(k1_relat_1(sK3),X0) )
    | spl4_9 ),
    inference(resolution,[],[f82,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f82,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f83,plain,
    ( ~ spl4_9
    | spl4_6 ),
    inference(avatar_split_clause,[],[f74,f64,f80])).

fof(f64,plain,
    ( spl4_6
  <=> r1_xboole_0(sK1,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f74,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK1)
    | spl4_6 ),
    inference(resolution,[],[f66,f25])).

fof(f66,plain,
    ( ~ r1_xboole_0(sK1,k1_relat_1(sK3))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f72,plain,
    ( spl4_7
    | spl4_5 ),
    inference(avatar_split_clause,[],[f68,f60,f70])).

fof(f60,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_5 ),
    inference(resolution,[],[f62,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f62,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f67,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_4 ),
    inference(avatar_split_clause,[],[f58,f53,f64,f60])).

fof(f53,plain,
    ( spl4_4
  <=> k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f58,plain,
    ( ~ r1_xboole_0(sK1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f57])).

fof(f57,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_4 ),
    inference(superposition,[],[f55,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f55,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f56,plain,
    ( ~ spl4_4
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f51,f44,f34,f53])).

fof(f34,plain,
    ( spl4_1
  <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f51,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f50,f46])).

fof(f50,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | spl4_1 ),
    inference(superposition,[],[f36,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f36,plain,
    ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f47,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

fof(f42,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f23,f34])).

fof(f23,plain,(
    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
