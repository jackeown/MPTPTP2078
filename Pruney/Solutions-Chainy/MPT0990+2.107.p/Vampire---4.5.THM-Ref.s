%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:47 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 361 expanded)
%              Number of leaves         :   47 ( 135 expanded)
%              Depth                    :   10
%              Number of atoms          :  672 (1674 expanded)
%              Number of equality atoms :  123 ( 437 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2805,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f170,f179,f183,f187,f290,f292,f329,f568,f879,f881,f908,f921,f928,f949,f971,f978,f980,f988,f1101,f2357,f2367,f2403,f2407,f2473,f2477,f2578,f2735])).

fof(f2735,plain,(
    ~ spl4_233 ),
    inference(avatar_contradiction_clause,[],[f2647])).

fof(f2647,plain,
    ( $false
    | ~ spl4_233 ),
    inference(subsumption_resolution,[],[f89,f2577])).

fof(f2577,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_233 ),
    inference(avatar_component_clause,[],[f2575])).

fof(f2575,plain,
    ( spl4_233
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_233])])).

fof(f89,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f35,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f2578,plain,
    ( ~ spl4_1
    | ~ spl4_60
    | ~ spl4_53
    | spl4_233
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f2556,f934,f2575,f870,f938,f163])).

fof(f163,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f938,plain,
    ( spl4_60
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f870,plain,
    ( spl4_53
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f934,plain,
    ( spl4_59
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f2556,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_59 ),
    inference(superposition,[],[f116,f936])).

fof(f936,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f934])).

fof(f116,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f2477,plain,(
    spl4_222 ),
    inference(avatar_contradiction_clause,[],[f2474])).

fof(f2474,plain,
    ( $false
    | spl4_222 ),
    inference(unit_resulting_resolution,[],[f144,f2472])).

fof(f2472,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_222 ),
    inference(avatar_component_clause,[],[f2470])).

fof(f2470,plain,
    ( spl4_222
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_222])])).

fof(f144,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f96,f93])).

fof(f93,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f96,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f2473,plain,
    ( ~ spl4_53
    | ~ spl4_1
    | spl4_60
    | ~ spl4_222
    | ~ spl4_22
    | ~ spl4_58
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f2468,f946,f914,f566,f2470,f938,f163,f870])).

fof(f566,plain,
    ( spl4_22
  <=> ! [X7] :
        ( sK1 != k1_relat_1(X7)
        | v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v2_funct_1(k5_relat_1(sK2,X7))
        | ~ v1_funct_1(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f914,plain,
    ( spl4_58
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f946,plain,
    ( spl4_62
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f2468,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_22
    | ~ spl4_58
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f2432,f916])).

fof(f916,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f914])).

fof(f2432,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_22
    | ~ spl4_62 ),
    inference(trivial_inequality_removal,[],[f2430])).

fof(f2430,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_22
    | ~ spl4_62 ),
    inference(superposition,[],[f567,f947])).

fof(f947,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f946])).

fof(f567,plain,
    ( ! [X7] :
        ( sK1 != k1_relat_1(X7)
        | v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v2_funct_1(k5_relat_1(sK2,X7))
        | ~ v1_funct_1(X7) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f566])).

fof(f2407,plain,(
    spl4_211 ),
    inference(avatar_contradiction_clause,[],[f2404])).

fof(f2404,plain,
    ( $false
    | spl4_211 ),
    inference(subsumption_resolution,[],[f202,f2386])).

fof(f2386,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl4_211 ),
    inference(avatar_component_clause,[],[f2384])).

fof(f2384,plain,
    ( spl4_211
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_211])])).

fof(f202,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f135,f92])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2403,plain,
    ( ~ spl4_211
    | ~ spl4_3
    | spl4_62
    | ~ spl4_6
    | ~ spl4_208 ),
    inference(avatar_split_clause,[],[f2402,f2350,f286,f946,f172,f2384])).

fof(f172,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f286,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f2350,plain,
    ( spl4_208
  <=> k1_relat_1(sK3) = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_208])])).

fof(f2402,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ spl4_6
    | ~ spl4_208 ),
    inference(forward_demodulation,[],[f2381,f288])).

fof(f288,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f286])).

fof(f2381,plain,
    ( k1_relat_1(sK3) = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ spl4_208 ),
    inference(superposition,[],[f217,f2352])).

fof(f2352,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ spl4_208 ),
    inference(avatar_component_clause,[],[f2350])).

fof(f217,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f124,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f124,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f2367,plain,
    ( ~ spl4_1
    | spl4_209 ),
    inference(avatar_contradiction_clause,[],[f2365])).

fof(f2365,plain,
    ( $false
    | ~ spl4_1
    | spl4_209 ),
    inference(unit_resulting_resolution,[],[f165,f201,f2356,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f2356,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl4_209 ),
    inference(avatar_component_clause,[],[f2354])).

fof(f2354,plain,
    ( spl4_209
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_209])])).

fof(f201,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f135,f83])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f165,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f163])).

fof(f2357,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_7
    | spl4_208
    | ~ spl4_209
    | ~ spl4_6
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f2348,f914,f286,f2354,f2350,f300,f172,f163])).

fof(f300,plain,
    ( spl4_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f2348,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f2347,f288])).

fof(f2347,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f2295,f149])).

fof(f149,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f101,f93])).

fof(f101,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f2295,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_58 ),
    inference(superposition,[],[f417,f916])).

fof(f417,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) = k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2)))
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X2),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f406])).

fof(f406,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) = k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2)))
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X2),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f129,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f129,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1101,plain,
    ( spl4_61
    | ~ spl4_67 ),
    inference(avatar_contradiction_clause,[],[f1100])).

fof(f1100,plain,
    ( $false
    | spl4_61
    | ~ spl4_67 ),
    inference(trivial_inequality_removal,[],[f1099])).

fof(f1099,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_61
    | ~ spl4_67 ),
    inference(forward_demodulation,[],[f944,f986])).

fof(f986,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_67 ),
    inference(avatar_component_clause,[],[f984])).

fof(f984,plain,
    ( spl4_67
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f944,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_61 ),
    inference(avatar_component_clause,[],[f942])).

fof(f942,plain,
    ( spl4_61
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f988,plain,
    ( ~ spl4_52
    | spl4_67
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f982,f960,f984,f866])).

fof(f866,plain,
    ( spl4_52
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f960,plain,
    ( spl4_63
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f982,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_63 ),
    inference(superposition,[],[f134,f962])).

fof(f962,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f960])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f980,plain,(
    spl4_65 ),
    inference(avatar_contradiction_clause,[],[f979])).

fof(f979,plain,
    ( $false
    | spl4_65 ),
    inference(subsumption_resolution,[],[f82,f970])).

fof(f970,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_65 ),
    inference(avatar_component_clause,[],[f968])).

fof(f968,plain,
    ( spl4_65
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f82,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f978,plain,(
    spl4_64 ),
    inference(avatar_contradiction_clause,[],[f977])).

fof(f977,plain,
    ( $false
    | spl4_64 ),
    inference(subsumption_resolution,[],[f91,f966])).

fof(f966,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_64 ),
    inference(avatar_component_clause,[],[f964])).

fof(f964,plain,
    ( spl4_64
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f91,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f971,plain,
    ( spl4_63
    | ~ spl4_53
    | ~ spl4_5
    | ~ spl4_64
    | ~ spl4_7
    | ~ spl4_52
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f955,f968,f866,f300,f964,f282,f870,f960])).

fof(f282,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f955,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f137,f85])).

fof(f85,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f949,plain,
    ( spl4_59
    | ~ spl4_1
    | ~ spl4_60
    | ~ spl4_7
    | ~ spl4_3
    | ~ spl4_53
    | ~ spl4_61
    | ~ spl4_62
    | ~ spl4_6
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f932,f914,f286,f946,f942,f870,f172,f300,f938,f163,f934])).

fof(f932,plain,
    ( sK1 != k1_relat_1(sK3)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f931,f288])).

fof(f931,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_58 ),
    inference(superposition,[],[f152,f916])).

fof(f152,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f120,f93])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f928,plain,
    ( ~ spl4_7
    | ~ spl4_52
    | ~ spl4_53
    | ~ spl4_5
    | spl4_58
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f925,f905,f914,f282,f870,f866,f300])).

fof(f905,plain,
    ( spl4_56
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f925,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_56 ),
    inference(superposition,[],[f140,f907])).

fof(f907,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f905])).

fof(f140,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f921,plain,(
    spl4_55 ),
    inference(avatar_contradiction_clause,[],[f918])).

fof(f918,plain,
    ( $false
    | spl4_55 ),
    inference(unit_resulting_resolution,[],[f90,f81,f83,f92,f903,f142])).

fof(f142,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f903,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_55 ),
    inference(avatar_component_clause,[],[f901])).

fof(f901,plain,
    ( spl4_55
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f81,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f908,plain,
    ( ~ spl4_55
    | spl4_56 ),
    inference(avatar_split_clause,[],[f898,f905,f901])).

fof(f898,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f665,f85])).

fof(f665,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_partfun1(X3))
      | k6_partfun1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f139,f100])).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f881,plain,(
    spl4_53 ),
    inference(avatar_contradiction_clause,[],[f880])).

fof(f880,plain,
    ( $false
    | spl4_53 ),
    inference(subsumption_resolution,[],[f81,f872])).

fof(f872,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_53 ),
    inference(avatar_component_clause,[],[f870])).

fof(f879,plain,(
    spl4_52 ),
    inference(avatar_contradiction_clause,[],[f878])).

fof(f878,plain,
    ( $false
    | spl4_52 ),
    inference(subsumption_resolution,[],[f83,f868])).

fof(f868,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_52 ),
    inference(avatar_component_clause,[],[f866])).

fof(f568,plain,
    ( ~ spl4_7
    | ~ spl4_3
    | spl4_22
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f564,f286,f566,f172,f300])).

fof(f564,plain,
    ( ! [X7] :
        ( sK1 != k1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v2_funct_1(k5_relat_1(sK2,X7))
        | ~ v1_relat_1(X7)
        | v2_funct_1(X7) )
    | ~ spl4_6 ),
    inference(superposition,[],[f122,f288])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f329,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f90,f302])).

fof(f302,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f300])).

fof(f292,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f92,f284])).

fof(f284,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f282])).

fof(f290,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f280,f286,f282])).

fof(f280,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f84,f134])).

fof(f84,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f187,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f123,f178])).

fof(f178,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f123,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f183,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f123,f169])).

fof(f169,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f179,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f160,f176,f172])).

fof(f160,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f108,f92])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f170,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f159,f167,f163])).

fof(f159,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f108,f83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (812843008)
% 0.13/0.37  ipcrm: permission denied for id (815529987)
% 0.13/0.37  ipcrm: permission denied for id (815562756)
% 0.13/0.37  ipcrm: permission denied for id (815595525)
% 0.13/0.37  ipcrm: permission denied for id (815628294)
% 0.13/0.37  ipcrm: permission denied for id (815661063)
% 0.13/0.37  ipcrm: permission denied for id (815693832)
% 0.13/0.38  ipcrm: permission denied for id (813006858)
% 0.13/0.38  ipcrm: permission denied for id (813039627)
% 0.13/0.38  ipcrm: permission denied for id (815759372)
% 0.13/0.38  ipcrm: permission denied for id (815857679)
% 0.13/0.38  ipcrm: permission denied for id (813170704)
% 0.13/0.39  ipcrm: permission denied for id (813236242)
% 0.13/0.39  ipcrm: permission denied for id (815923219)
% 0.13/0.39  ipcrm: permission denied for id (815955988)
% 0.13/0.39  ipcrm: permission denied for id (816021526)
% 0.13/0.39  ipcrm: permission denied for id (816054295)
% 0.13/0.39  ipcrm: permission denied for id (816087064)
% 0.13/0.40  ipcrm: permission denied for id (816152602)
% 0.13/0.40  ipcrm: permission denied for id (816185371)
% 0.20/0.40  ipcrm: permission denied for id (816283678)
% 0.20/0.40  ipcrm: permission denied for id (813432864)
% 0.20/0.40  ipcrm: permission denied for id (813465633)
% 0.20/0.41  ipcrm: permission denied for id (816349218)
% 0.20/0.41  ipcrm: permission denied for id (816414756)
% 0.20/0.41  ipcrm: permission denied for id (816447525)
% 0.20/0.41  ipcrm: permission denied for id (816513063)
% 0.20/0.41  ipcrm: permission denied for id (813596713)
% 0.20/0.42  ipcrm: permission denied for id (813629482)
% 0.20/0.42  ipcrm: permission denied for id (816578603)
% 0.20/0.42  ipcrm: permission denied for id (816611372)
% 0.20/0.42  ipcrm: permission denied for id (813727789)
% 0.20/0.42  ipcrm: permission denied for id (816709680)
% 0.20/0.42  ipcrm: permission denied for id (816742449)
% 0.20/0.43  ipcrm: permission denied for id (813793332)
% 0.20/0.43  ipcrm: permission denied for id (816873526)
% 0.20/0.43  ipcrm: permission denied for id (816939064)
% 0.20/0.43  ipcrm: permission denied for id (816971833)
% 0.20/0.44  ipcrm: permission denied for id (817004602)
% 0.20/0.44  ipcrm: permission denied for id (813891643)
% 0.20/0.44  ipcrm: permission denied for id (817037372)
% 0.20/0.44  ipcrm: permission denied for id (817168448)
% 0.20/0.44  ipcrm: permission denied for id (814055489)
% 0.20/0.45  ipcrm: permission denied for id (814088258)
% 0.20/0.45  ipcrm: permission denied for id (817201219)
% 0.20/0.45  ipcrm: permission denied for id (817266757)
% 0.20/0.45  ipcrm: permission denied for id (817299526)
% 0.20/0.45  ipcrm: permission denied for id (814153799)
% 0.20/0.45  ipcrm: permission denied for id (814186568)
% 0.20/0.45  ipcrm: permission denied for id (817332297)
% 0.20/0.46  ipcrm: permission denied for id (817397835)
% 0.20/0.46  ipcrm: permission denied for id (814252108)
% 0.20/0.46  ipcrm: permission denied for id (817463374)
% 0.20/0.46  ipcrm: permission denied for id (817496143)
% 0.20/0.46  ipcrm: permission denied for id (814317648)
% 0.20/0.46  ipcrm: permission denied for id (817528913)
% 0.20/0.47  ipcrm: permission denied for id (814350418)
% 0.20/0.47  ipcrm: permission denied for id (817594452)
% 0.20/0.47  ipcrm: permission denied for id (814448725)
% 0.20/0.47  ipcrm: permission denied for id (814481494)
% 0.20/0.47  ipcrm: permission denied for id (817627223)
% 0.20/0.48  ipcrm: permission denied for id (814547033)
% 0.20/0.48  ipcrm: permission denied for id (817692762)
% 0.20/0.48  ipcrm: permission denied for id (814579803)
% 0.20/0.48  ipcrm: permission denied for id (814645341)
% 0.20/0.48  ipcrm: permission denied for id (814678110)
% 0.20/0.48  ipcrm: permission denied for id (814710879)
% 0.20/0.49  ipcrm: permission denied for id (814743649)
% 0.20/0.49  ipcrm: permission denied for id (817791074)
% 0.20/0.49  ipcrm: permission denied for id (814841957)
% 0.20/0.49  ipcrm: permission denied for id (814874726)
% 0.20/0.49  ipcrm: permission denied for id (817922152)
% 0.20/0.50  ipcrm: permission denied for id (814907497)
% 0.20/0.50  ipcrm: permission denied for id (814940268)
% 0.20/0.50  ipcrm: permission denied for id (818020461)
% 0.20/0.50  ipcrm: permission denied for id (818085998)
% 0.20/0.50  ipcrm: permission denied for id (815038575)
% 0.20/0.50  ipcrm: permission denied for id (818118768)
% 0.20/0.51  ipcrm: permission denied for id (818184306)
% 0.20/0.51  ipcrm: permission denied for id (818249844)
% 0.20/0.51  ipcrm: permission denied for id (815235190)
% 0.20/0.51  ipcrm: permission denied for id (815267959)
% 0.20/0.52  ipcrm: permission denied for id (815333498)
% 0.20/0.52  ipcrm: permission denied for id (818413691)
% 0.20/0.52  ipcrm: permission denied for id (815366268)
% 0.20/0.52  ipcrm: permission denied for id (818446461)
% 0.76/0.65  % (10016)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.76/0.66  % (10039)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.16/0.66  % (10031)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.19/0.67  % (10023)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.19/0.67  % (10014)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.19/0.67  % (10028)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.19/0.68  % (10030)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.19/0.68  % (10031)Refutation not found, incomplete strategy% (10031)------------------------------
% 1.19/0.68  % (10031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.69  % (10015)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.19/0.69  % (10020)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.69  % (10031)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.69  
% 1.19/0.69  % (10031)Memory used [KB]: 10746
% 1.19/0.69  % (10031)Time elapsed: 0.116 s
% 1.19/0.69  % (10031)------------------------------
% 1.19/0.69  % (10031)------------------------------
% 1.19/0.69  % (10018)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.19/0.69  % (10022)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.19/0.69  % (10029)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.19/0.69  % (10041)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.19/0.69  % (10017)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.19/0.70  % (10037)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.19/0.70  % (10038)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.19/0.70  % (10033)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.19/0.70  % (10036)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.19/0.70  % (10025)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.19/0.70  % (10019)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.19/0.70  % (10021)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.51/0.70  % (10043)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.51/0.71  % (10040)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.51/0.71  % (10034)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.51/0.71  % (10026)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.51/0.71  % (10027)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.51/0.72  % (10042)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.51/0.72  % (10044)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.51/0.72  % (10035)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.51/0.73  % (10032)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.74/0.83  % (10123)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.74/0.83  % (10028)Refutation found. Thanks to Tanya!
% 1.74/0.83  % SZS status Theorem for theBenchmark
% 1.74/0.83  % SZS output start Proof for theBenchmark
% 1.74/0.83  fof(f2805,plain,(
% 1.74/0.83    $false),
% 1.74/0.83    inference(avatar_sat_refutation,[],[f170,f179,f183,f187,f290,f292,f329,f568,f879,f881,f908,f921,f928,f949,f971,f978,f980,f988,f1101,f2357,f2367,f2403,f2407,f2473,f2477,f2578,f2735])).
% 1.74/0.83  fof(f2735,plain,(
% 1.74/0.83    ~spl4_233),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f2647])).
% 1.74/0.83  fof(f2647,plain,(
% 1.74/0.83    $false | ~spl4_233),
% 1.74/0.83    inference(subsumption_resolution,[],[f89,f2577])).
% 1.74/0.83  fof(f2577,plain,(
% 1.74/0.83    sK3 = k2_funct_1(sK2) | ~spl4_233),
% 1.74/0.83    inference(avatar_component_clause,[],[f2575])).
% 1.74/0.83  fof(f2575,plain,(
% 1.74/0.83    spl4_233 <=> sK3 = k2_funct_1(sK2)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_233])])).
% 1.74/0.83  fof(f89,plain,(
% 1.74/0.83    sK3 != k2_funct_1(sK2)),
% 1.74/0.83    inference(cnf_transformation,[],[f38])).
% 1.74/0.83  fof(f38,plain,(
% 1.74/0.83    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.74/0.83    inference(flattening,[],[f37])).
% 1.74/0.83  fof(f37,plain,(
% 1.74/0.83    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.74/0.83    inference(ennf_transformation,[],[f36])).
% 1.74/0.83  fof(f36,negated_conjecture,(
% 1.74/0.83    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.74/0.83    inference(negated_conjecture,[],[f35])).
% 1.74/0.83  fof(f35,conjecture,(
% 1.74/0.83    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.74/0.83  fof(f2578,plain,(
% 1.74/0.83    ~spl4_1 | ~spl4_60 | ~spl4_53 | spl4_233 | ~spl4_59),
% 1.74/0.83    inference(avatar_split_clause,[],[f2556,f934,f2575,f870,f938,f163])).
% 1.74/0.83  fof(f163,plain,(
% 1.74/0.83    spl4_1 <=> v1_relat_1(sK3)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.74/0.83  fof(f938,plain,(
% 1.74/0.83    spl4_60 <=> v2_funct_1(sK3)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 1.74/0.83  fof(f870,plain,(
% 1.74/0.83    spl4_53 <=> v1_funct_1(sK3)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 1.74/0.83  fof(f934,plain,(
% 1.74/0.83    spl4_59 <=> sK2 = k2_funct_1(sK3)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 1.74/0.83  fof(f2556,plain,(
% 1.74/0.83    sK3 = k2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_59),
% 1.74/0.83    inference(superposition,[],[f116,f936])).
% 1.74/0.83  fof(f936,plain,(
% 1.74/0.83    sK2 = k2_funct_1(sK3) | ~spl4_59),
% 1.74/0.83    inference(avatar_component_clause,[],[f934])).
% 1.74/0.83  fof(f116,plain,(
% 1.74/0.83    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f52])).
% 1.74/0.83  fof(f52,plain,(
% 1.74/0.83    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.83    inference(flattening,[],[f51])).
% 1.74/0.83  fof(f51,plain,(
% 1.74/0.83    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.83    inference(ennf_transformation,[],[f23])).
% 1.74/0.83  fof(f23,axiom,(
% 1.74/0.83    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 1.74/0.83  fof(f2477,plain,(
% 1.74/0.83    spl4_222),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f2474])).
% 1.74/0.83  fof(f2474,plain,(
% 1.74/0.83    $false | spl4_222),
% 1.74/0.83    inference(unit_resulting_resolution,[],[f144,f2472])).
% 1.74/0.83  fof(f2472,plain,(
% 1.74/0.83    ~v2_funct_1(k6_partfun1(sK0)) | spl4_222),
% 1.74/0.83    inference(avatar_component_clause,[],[f2470])).
% 1.74/0.83  fof(f2470,plain,(
% 1.74/0.83    spl4_222 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_222])])).
% 1.74/0.83  fof(f144,plain,(
% 1.74/0.83    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.74/0.83    inference(definition_unfolding,[],[f96,f93])).
% 1.74/0.83  fof(f93,plain,(
% 1.74/0.83    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f32])).
% 1.74/0.83  fof(f32,axiom,(
% 1.74/0.83    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.74/0.83  fof(f96,plain,(
% 1.74/0.83    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.74/0.83    inference(cnf_transformation,[],[f15])).
% 1.74/0.83  fof(f15,axiom,(
% 1.74/0.83    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.74/0.83  fof(f2473,plain,(
% 1.74/0.83    ~spl4_53 | ~spl4_1 | spl4_60 | ~spl4_222 | ~spl4_22 | ~spl4_58 | ~spl4_62),
% 1.74/0.83    inference(avatar_split_clause,[],[f2468,f946,f914,f566,f2470,f938,f163,f870])).
% 1.74/0.83  fof(f566,plain,(
% 1.74/0.83    spl4_22 <=> ! [X7] : (sK1 != k1_relat_1(X7) | v2_funct_1(X7) | ~v1_relat_1(X7) | ~v2_funct_1(k5_relat_1(sK2,X7)) | ~v1_funct_1(X7))),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.74/0.83  fof(f914,plain,(
% 1.74/0.83    spl4_58 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 1.74/0.83  fof(f946,plain,(
% 1.74/0.83    spl4_62 <=> sK1 = k1_relat_1(sK3)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 1.74/0.83  fof(f2468,plain,(
% 1.74/0.83    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | (~spl4_22 | ~spl4_58 | ~spl4_62)),
% 1.74/0.83    inference(forward_demodulation,[],[f2432,f916])).
% 1.74/0.83  fof(f916,plain,(
% 1.74/0.83    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_58),
% 1.74/0.83    inference(avatar_component_clause,[],[f914])).
% 1.74/0.83  fof(f2432,plain,(
% 1.74/0.83    v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | (~spl4_22 | ~spl4_62)),
% 1.74/0.83    inference(trivial_inequality_removal,[],[f2430])).
% 1.74/0.83  fof(f2430,plain,(
% 1.74/0.83    sK1 != sK1 | v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | (~spl4_22 | ~spl4_62)),
% 1.74/0.83    inference(superposition,[],[f567,f947])).
% 1.74/0.83  fof(f947,plain,(
% 1.74/0.83    sK1 = k1_relat_1(sK3) | ~spl4_62),
% 1.74/0.83    inference(avatar_component_clause,[],[f946])).
% 1.74/0.83  fof(f567,plain,(
% 1.74/0.83    ( ! [X7] : (sK1 != k1_relat_1(X7) | v2_funct_1(X7) | ~v1_relat_1(X7) | ~v2_funct_1(k5_relat_1(sK2,X7)) | ~v1_funct_1(X7)) ) | ~spl4_22),
% 1.74/0.83    inference(avatar_component_clause,[],[f566])).
% 1.74/0.83  fof(f2407,plain,(
% 1.74/0.83    spl4_211),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f2404])).
% 1.74/0.83  fof(f2404,plain,(
% 1.74/0.83    $false | spl4_211),
% 1.74/0.83    inference(subsumption_resolution,[],[f202,f2386])).
% 1.74/0.83  fof(f2386,plain,(
% 1.74/0.83    ~v4_relat_1(sK2,sK0) | spl4_211),
% 1.74/0.83    inference(avatar_component_clause,[],[f2384])).
% 1.74/0.83  fof(f2384,plain,(
% 1.74/0.83    spl4_211 <=> v4_relat_1(sK2,sK0)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_211])])).
% 1.74/0.83  fof(f202,plain,(
% 1.74/0.83    v4_relat_1(sK2,sK0)),
% 1.74/0.83    inference(resolution,[],[f135,f92])).
% 1.74/0.83  fof(f92,plain,(
% 1.74/0.83    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.74/0.83    inference(cnf_transformation,[],[f38])).
% 1.74/0.83  fof(f135,plain,(
% 1.74/0.83    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f72])).
% 1.74/0.83  fof(f72,plain,(
% 1.74/0.83    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.83    inference(ennf_transformation,[],[f26])).
% 1.74/0.83  fof(f26,axiom,(
% 1.74/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.74/0.83  fof(f2403,plain,(
% 1.74/0.83    ~spl4_211 | ~spl4_3 | spl4_62 | ~spl4_6 | ~spl4_208),
% 1.74/0.83    inference(avatar_split_clause,[],[f2402,f2350,f286,f946,f172,f2384])).
% 1.74/0.83  fof(f172,plain,(
% 1.74/0.83    spl4_3 <=> v1_relat_1(sK2)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.74/0.83  fof(f286,plain,(
% 1.74/0.83    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.74/0.83  fof(f2350,plain,(
% 1.74/0.83    spl4_208 <=> k1_relat_1(sK3) = k9_relat_1(sK2,sK0)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_208])])).
% 1.74/0.83  fof(f2402,plain,(
% 1.74/0.83    sK1 = k1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | (~spl4_6 | ~spl4_208)),
% 1.74/0.83    inference(forward_demodulation,[],[f2381,f288])).
% 1.74/0.83  fof(f288,plain,(
% 1.74/0.83    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 1.74/0.83    inference(avatar_component_clause,[],[f286])).
% 1.74/0.83  fof(f2381,plain,(
% 1.74/0.83    k1_relat_1(sK3) = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | ~spl4_208),
% 1.74/0.83    inference(superposition,[],[f217,f2352])).
% 1.74/0.83  fof(f2352,plain,(
% 1.74/0.83    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~spl4_208),
% 1.74/0.83    inference(avatar_component_clause,[],[f2350])).
% 1.74/0.83  fof(f217,plain,(
% 1.74/0.83    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 1.74/0.83    inference(duplicate_literal_removal,[],[f216])).
% 1.74/0.83  fof(f216,plain,(
% 1.74/0.83    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.74/0.83    inference(superposition,[],[f124,f130])).
% 1.74/0.83  fof(f130,plain,(
% 1.74/0.83    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f70])).
% 1.74/0.83  fof(f70,plain,(
% 1.74/0.83    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.74/0.83    inference(flattening,[],[f69])).
% 1.74/0.83  fof(f69,plain,(
% 1.74/0.83    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.74/0.83    inference(ennf_transformation,[],[f9])).
% 1.74/0.83  fof(f9,axiom,(
% 1.74/0.83    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.74/0.83  fof(f124,plain,(
% 1.74/0.83    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f61])).
% 1.74/0.83  fof(f61,plain,(
% 1.74/0.83    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.74/0.83    inference(ennf_transformation,[],[f6])).
% 1.74/0.83  fof(f6,axiom,(
% 1.74/0.83    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.74/0.83  fof(f2367,plain,(
% 1.74/0.83    ~spl4_1 | spl4_209),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f2365])).
% 1.74/0.83  fof(f2365,plain,(
% 1.74/0.83    $false | (~spl4_1 | spl4_209)),
% 1.74/0.83    inference(unit_resulting_resolution,[],[f165,f201,f2356,f126])).
% 1.74/0.83  fof(f126,plain,(
% 1.74/0.83    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f62])).
% 1.74/0.83  fof(f62,plain,(
% 1.74/0.83    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.74/0.83    inference(ennf_transformation,[],[f3])).
% 1.74/0.83  fof(f3,axiom,(
% 1.74/0.83    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.74/0.83  fof(f2356,plain,(
% 1.74/0.83    ~r1_tarski(k1_relat_1(sK3),sK1) | spl4_209),
% 1.74/0.83    inference(avatar_component_clause,[],[f2354])).
% 1.74/0.83  fof(f2354,plain,(
% 1.74/0.83    spl4_209 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_209])])).
% 1.74/0.83  fof(f201,plain,(
% 1.74/0.83    v4_relat_1(sK3,sK1)),
% 1.74/0.83    inference(resolution,[],[f135,f83])).
% 1.74/0.83  fof(f83,plain,(
% 1.74/0.83    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.74/0.83    inference(cnf_transformation,[],[f38])).
% 1.74/0.83  fof(f165,plain,(
% 1.74/0.83    v1_relat_1(sK3) | ~spl4_1),
% 1.74/0.83    inference(avatar_component_clause,[],[f163])).
% 1.74/0.83  fof(f2357,plain,(
% 1.74/0.83    ~spl4_1 | ~spl4_3 | ~spl4_7 | spl4_208 | ~spl4_209 | ~spl4_6 | ~spl4_58),
% 1.74/0.83    inference(avatar_split_clause,[],[f2348,f914,f286,f2354,f2350,f300,f172,f163])).
% 1.74/0.83  fof(f300,plain,(
% 1.74/0.83    spl4_7 <=> v1_funct_1(sK2)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.74/0.83  fof(f2348,plain,(
% 1.74/0.83    ~r1_tarski(k1_relat_1(sK3),sK1) | k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | (~spl4_6 | ~spl4_58)),
% 1.74/0.83    inference(forward_demodulation,[],[f2347,f288])).
% 1.74/0.83  fof(f2347,plain,(
% 1.74/0.83    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_58),
% 1.74/0.83    inference(forward_demodulation,[],[f2295,f149])).
% 1.74/0.83  fof(f149,plain,(
% 1.74/0.83    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.74/0.83    inference(definition_unfolding,[],[f101,f93])).
% 1.74/0.83  fof(f101,plain,(
% 1.74/0.83    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.74/0.83    inference(cnf_transformation,[],[f10])).
% 1.74/0.83  fof(f10,axiom,(
% 1.74/0.83    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.74/0.83  fof(f2295,plain,(
% 1.74/0.83    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_58),
% 1.74/0.83    inference(superposition,[],[f417,f916])).
% 1.74/0.83  fof(f417,plain,(
% 1.74/0.83    ( ! [X2,X1] : (k1_relat_1(X2) = k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X2),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2)) )),
% 1.74/0.83    inference(duplicate_literal_removal,[],[f406])).
% 1.74/0.83  fof(f406,plain,(
% 1.74/0.83    ( ! [X2,X1] : (k1_relat_1(X2) = k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X2),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.74/0.83    inference(superposition,[],[f129,f107])).
% 1.74/0.83  fof(f107,plain,(
% 1.74/0.83    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f43])).
% 1.74/0.83  fof(f43,plain,(
% 1.74/0.83    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.74/0.83    inference(ennf_transformation,[],[f8])).
% 1.74/0.83  fof(f8,axiom,(
% 1.74/0.83    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.74/0.83  fof(f129,plain,(
% 1.74/0.83    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f68])).
% 1.74/0.83  fof(f68,plain,(
% 1.74/0.83    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.74/0.83    inference(flattening,[],[f67])).
% 1.74/0.83  fof(f67,plain,(
% 1.74/0.83    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.74/0.83    inference(ennf_transformation,[],[f17])).
% 1.74/0.83  fof(f17,axiom,(
% 1.74/0.83    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.74/0.83  fof(f1101,plain,(
% 1.74/0.83    spl4_61 | ~spl4_67),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f1100])).
% 1.74/0.83  fof(f1100,plain,(
% 1.74/0.83    $false | (spl4_61 | ~spl4_67)),
% 1.74/0.83    inference(trivial_inequality_removal,[],[f1099])).
% 1.74/0.83  fof(f1099,plain,(
% 1.74/0.83    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_61 | ~spl4_67)),
% 1.74/0.83    inference(forward_demodulation,[],[f944,f986])).
% 1.74/0.83  fof(f986,plain,(
% 1.74/0.83    sK0 = k2_relat_1(sK3) | ~spl4_67),
% 1.74/0.83    inference(avatar_component_clause,[],[f984])).
% 1.74/0.83  fof(f984,plain,(
% 1.74/0.83    spl4_67 <=> sK0 = k2_relat_1(sK3)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 1.74/0.83  fof(f944,plain,(
% 1.74/0.83    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_61),
% 1.74/0.83    inference(avatar_component_clause,[],[f942])).
% 1.74/0.83  fof(f942,plain,(
% 1.74/0.83    spl4_61 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 1.74/0.83  fof(f988,plain,(
% 1.74/0.83    ~spl4_52 | spl4_67 | ~spl4_63),
% 1.74/0.83    inference(avatar_split_clause,[],[f982,f960,f984,f866])).
% 1.74/0.83  fof(f866,plain,(
% 1.74/0.83    spl4_52 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.74/0.83  fof(f960,plain,(
% 1.74/0.83    spl4_63 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 1.74/0.83  fof(f982,plain,(
% 1.74/0.83    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_63),
% 1.74/0.83    inference(superposition,[],[f134,f962])).
% 1.74/0.83  fof(f962,plain,(
% 1.74/0.83    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_63),
% 1.74/0.83    inference(avatar_component_clause,[],[f960])).
% 1.74/0.83  fof(f134,plain,(
% 1.74/0.83    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.74/0.83    inference(cnf_transformation,[],[f71])).
% 1.74/0.83  fof(f71,plain,(
% 1.74/0.83    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.83    inference(ennf_transformation,[],[f27])).
% 1.74/0.83  fof(f27,axiom,(
% 1.74/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.74/0.83  fof(f980,plain,(
% 1.74/0.83    spl4_65),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f979])).
% 1.74/0.83  fof(f979,plain,(
% 1.74/0.83    $false | spl4_65),
% 1.74/0.83    inference(subsumption_resolution,[],[f82,f970])).
% 1.74/0.83  fof(f970,plain,(
% 1.74/0.83    ~v1_funct_2(sK3,sK1,sK0) | spl4_65),
% 1.74/0.83    inference(avatar_component_clause,[],[f968])).
% 1.74/0.83  fof(f968,plain,(
% 1.74/0.83    spl4_65 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 1.74/0.83  fof(f82,plain,(
% 1.74/0.83    v1_funct_2(sK3,sK1,sK0)),
% 1.74/0.83    inference(cnf_transformation,[],[f38])).
% 1.74/0.83  fof(f978,plain,(
% 1.74/0.83    spl4_64),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f977])).
% 1.74/0.83  fof(f977,plain,(
% 1.74/0.83    $false | spl4_64),
% 1.74/0.83    inference(subsumption_resolution,[],[f91,f966])).
% 1.74/0.83  fof(f966,plain,(
% 1.74/0.83    ~v1_funct_2(sK2,sK0,sK1) | spl4_64),
% 1.74/0.83    inference(avatar_component_clause,[],[f964])).
% 1.74/0.83  fof(f964,plain,(
% 1.74/0.83    spl4_64 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 1.74/0.83  fof(f91,plain,(
% 1.74/0.83    v1_funct_2(sK2,sK0,sK1)),
% 1.74/0.83    inference(cnf_transformation,[],[f38])).
% 1.74/0.83  fof(f971,plain,(
% 1.74/0.83    spl4_63 | ~spl4_53 | ~spl4_5 | ~spl4_64 | ~spl4_7 | ~spl4_52 | ~spl4_65),
% 1.74/0.83    inference(avatar_split_clause,[],[f955,f968,f866,f300,f964,f282,f870,f960])).
% 1.74/0.83  fof(f282,plain,(
% 1.74/0.83    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.74/0.83  fof(f955,plain,(
% 1.74/0.83    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.74/0.83    inference(resolution,[],[f137,f85])).
% 1.74/0.83  fof(f85,plain,(
% 1.74/0.83    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.74/0.83    inference(cnf_transformation,[],[f38])).
% 1.74/0.83  fof(f137,plain,(
% 1.74/0.83    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.74/0.83    inference(cnf_transformation,[],[f74])).
% 1.74/0.83  fof(f74,plain,(
% 1.74/0.83    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.74/0.83    inference(flattening,[],[f73])).
% 1.74/0.83  fof(f73,plain,(
% 1.74/0.83    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.74/0.83    inference(ennf_transformation,[],[f33])).
% 1.74/0.83  fof(f33,axiom,(
% 1.74/0.83    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.74/0.83  fof(f949,plain,(
% 1.74/0.83    spl4_59 | ~spl4_1 | ~spl4_60 | ~spl4_7 | ~spl4_3 | ~spl4_53 | ~spl4_61 | ~spl4_62 | ~spl4_6 | ~spl4_58),
% 1.74/0.83    inference(avatar_split_clause,[],[f932,f914,f286,f946,f942,f870,f172,f300,f938,f163,f934])).
% 1.74/0.83  fof(f932,plain,(
% 1.74/0.83    sK1 != k1_relat_1(sK3) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_6 | ~spl4_58)),
% 1.74/0.83    inference(forward_demodulation,[],[f931,f288])).
% 1.74/0.83  fof(f931,plain,(
% 1.74/0.83    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_58),
% 1.74/0.83    inference(superposition,[],[f152,f916])).
% 1.74/0.83  fof(f152,plain,(
% 1.74/0.83    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.74/0.83    inference(definition_unfolding,[],[f120,f93])).
% 1.74/0.83  fof(f120,plain,(
% 1.74/0.83    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1) )),
% 1.74/0.83    inference(cnf_transformation,[],[f58])).
% 1.74/0.83  fof(f58,plain,(
% 1.74/0.83    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.83    inference(flattening,[],[f57])).
% 1.74/0.83  fof(f57,plain,(
% 1.74/0.83    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.83    inference(ennf_transformation,[],[f22])).
% 1.74/0.83  fof(f22,axiom,(
% 1.74/0.83    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.74/0.83  fof(f928,plain,(
% 1.74/0.83    ~spl4_7 | ~spl4_52 | ~spl4_53 | ~spl4_5 | spl4_58 | ~spl4_56),
% 1.74/0.83    inference(avatar_split_clause,[],[f925,f905,f914,f282,f870,f866,f300])).
% 1.74/0.83  fof(f905,plain,(
% 1.74/0.83    spl4_56 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 1.74/0.83  fof(f925,plain,(
% 1.74/0.83    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_56),
% 1.74/0.83    inference(superposition,[],[f140,f907])).
% 1.74/0.83  fof(f907,plain,(
% 1.74/0.83    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_56),
% 1.74/0.83    inference(avatar_component_clause,[],[f905])).
% 1.74/0.83  fof(f140,plain,(
% 1.74/0.83    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f78])).
% 1.74/0.83  fof(f78,plain,(
% 1.74/0.83    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.74/0.83    inference(flattening,[],[f77])).
% 1.74/0.83  fof(f77,plain,(
% 1.74/0.83    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.74/0.83    inference(ennf_transformation,[],[f31])).
% 1.74/0.83  fof(f31,axiom,(
% 1.74/0.83    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.74/0.83  fof(f921,plain,(
% 1.74/0.83    spl4_55),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f918])).
% 1.74/0.83  fof(f918,plain,(
% 1.74/0.83    $false | spl4_55),
% 1.74/0.83    inference(unit_resulting_resolution,[],[f90,f81,f83,f92,f903,f142])).
% 1.74/0.83  fof(f142,plain,(
% 1.74/0.83    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f80])).
% 1.74/0.83  fof(f80,plain,(
% 1.74/0.83    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.74/0.83    inference(flattening,[],[f79])).
% 1.74/0.83  fof(f79,plain,(
% 1.74/0.83    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.74/0.83    inference(ennf_transformation,[],[f29])).
% 1.74/0.83  fof(f29,axiom,(
% 1.74/0.83    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.74/0.83  fof(f903,plain,(
% 1.74/0.83    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_55),
% 1.74/0.83    inference(avatar_component_clause,[],[f901])).
% 1.74/0.83  fof(f901,plain,(
% 1.74/0.83    spl4_55 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 1.74/0.83  fof(f81,plain,(
% 1.74/0.83    v1_funct_1(sK3)),
% 1.74/0.83    inference(cnf_transformation,[],[f38])).
% 1.74/0.83  fof(f90,plain,(
% 1.74/0.83    v1_funct_1(sK2)),
% 1.74/0.83    inference(cnf_transformation,[],[f38])).
% 1.74/0.83  fof(f908,plain,(
% 1.74/0.83    ~spl4_55 | spl4_56),
% 1.74/0.83    inference(avatar_split_clause,[],[f898,f905,f901])).
% 1.74/0.83  fof(f898,plain,(
% 1.74/0.83    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.74/0.83    inference(resolution,[],[f665,f85])).
% 1.74/0.83  fof(f665,plain,(
% 1.74/0.83    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_partfun1(X3)) | k6_partfun1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 1.74/0.83    inference(resolution,[],[f139,f100])).
% 1.74/0.83  fof(f100,plain,(
% 1.74/0.83    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.74/0.83    inference(cnf_transformation,[],[f30])).
% 1.74/0.83  fof(f30,axiom,(
% 1.74/0.83    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.74/0.83  fof(f139,plain,(
% 1.74/0.83    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f76])).
% 1.74/0.83  fof(f76,plain,(
% 1.74/0.83    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.83    inference(flattening,[],[f75])).
% 1.74/0.83  fof(f75,plain,(
% 1.74/0.83    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.74/0.83    inference(ennf_transformation,[],[f28])).
% 1.74/0.83  fof(f28,axiom,(
% 1.74/0.83    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.74/0.83  fof(f881,plain,(
% 1.74/0.83    spl4_53),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f880])).
% 1.74/0.83  fof(f880,plain,(
% 1.74/0.83    $false | spl4_53),
% 1.74/0.83    inference(subsumption_resolution,[],[f81,f872])).
% 1.74/0.83  fof(f872,plain,(
% 1.74/0.83    ~v1_funct_1(sK3) | spl4_53),
% 1.74/0.83    inference(avatar_component_clause,[],[f870])).
% 1.74/0.83  fof(f879,plain,(
% 1.74/0.83    spl4_52),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f878])).
% 1.74/0.83  fof(f878,plain,(
% 1.74/0.83    $false | spl4_52),
% 1.74/0.83    inference(subsumption_resolution,[],[f83,f868])).
% 1.74/0.83  fof(f868,plain,(
% 1.74/0.83    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_52),
% 1.74/0.83    inference(avatar_component_clause,[],[f866])).
% 1.74/0.83  fof(f568,plain,(
% 1.74/0.83    ~spl4_7 | ~spl4_3 | spl4_22 | ~spl4_6),
% 1.74/0.83    inference(avatar_split_clause,[],[f564,f286,f566,f172,f300])).
% 1.74/0.83  fof(f564,plain,(
% 1.74/0.83    ( ! [X7] : (sK1 != k1_relat_1(X7) | ~v1_funct_1(X7) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,X7)) | ~v1_relat_1(X7) | v2_funct_1(X7)) ) | ~spl4_6),
% 1.74/0.83    inference(superposition,[],[f122,f288])).
% 1.74/0.83  fof(f122,plain,(
% 1.74/0.83    ( ! [X0,X1] : (k1_relat_1(X0) != k2_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f60])).
% 1.74/0.83  fof(f60,plain,(
% 1.74/0.83    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.83    inference(flattening,[],[f59])).
% 1.74/0.83  fof(f59,plain,(
% 1.74/0.83    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.83    inference(ennf_transformation,[],[f20])).
% 1.74/0.83  fof(f20,axiom,(
% 1.74/0.83    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 1.74/0.83  fof(f329,plain,(
% 1.74/0.83    spl4_7),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f328])).
% 1.74/0.83  fof(f328,plain,(
% 1.74/0.83    $false | spl4_7),
% 1.74/0.83    inference(subsumption_resolution,[],[f90,f302])).
% 1.74/0.83  fof(f302,plain,(
% 1.74/0.83    ~v1_funct_1(sK2) | spl4_7),
% 1.74/0.83    inference(avatar_component_clause,[],[f300])).
% 1.74/0.83  fof(f292,plain,(
% 1.74/0.83    spl4_5),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f291])).
% 1.74/0.83  fof(f291,plain,(
% 1.74/0.83    $false | spl4_5),
% 1.74/0.83    inference(subsumption_resolution,[],[f92,f284])).
% 1.74/0.83  fof(f284,plain,(
% 1.74/0.83    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 1.74/0.83    inference(avatar_component_clause,[],[f282])).
% 1.74/0.83  fof(f290,plain,(
% 1.74/0.83    ~spl4_5 | spl4_6),
% 1.74/0.83    inference(avatar_split_clause,[],[f280,f286,f282])).
% 1.74/0.83  fof(f280,plain,(
% 1.74/0.83    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.74/0.83    inference(superposition,[],[f84,f134])).
% 1.74/0.83  fof(f84,plain,(
% 1.74/0.83    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.74/0.83    inference(cnf_transformation,[],[f38])).
% 1.74/0.83  fof(f187,plain,(
% 1.74/0.83    spl4_4),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f184])).
% 1.74/0.83  fof(f184,plain,(
% 1.74/0.83    $false | spl4_4),
% 1.74/0.83    inference(unit_resulting_resolution,[],[f123,f178])).
% 1.74/0.83  fof(f178,plain,(
% 1.74/0.83    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 1.74/0.83    inference(avatar_component_clause,[],[f176])).
% 1.74/0.83  fof(f176,plain,(
% 1.74/0.83    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.74/0.83  fof(f123,plain,(
% 1.74/0.83    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.74/0.83    inference(cnf_transformation,[],[f4])).
% 1.74/0.83  fof(f4,axiom,(
% 1.74/0.83    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.74/0.83  fof(f183,plain,(
% 1.74/0.83    spl4_2),
% 1.74/0.83    inference(avatar_contradiction_clause,[],[f180])).
% 1.74/0.83  fof(f180,plain,(
% 1.74/0.83    $false | spl4_2),
% 1.74/0.83    inference(unit_resulting_resolution,[],[f123,f169])).
% 1.74/0.83  fof(f169,plain,(
% 1.74/0.83    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 1.74/0.83    inference(avatar_component_clause,[],[f167])).
% 1.74/0.83  fof(f167,plain,(
% 1.74/0.83    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.74/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.74/0.83  fof(f179,plain,(
% 1.74/0.83    spl4_3 | ~spl4_4),
% 1.74/0.83    inference(avatar_split_clause,[],[f160,f176,f172])).
% 1.74/0.83  fof(f160,plain,(
% 1.74/0.83    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 1.74/0.83    inference(resolution,[],[f108,f92])).
% 1.74/0.83  fof(f108,plain,(
% 1.74/0.83    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.74/0.83    inference(cnf_transformation,[],[f44])).
% 1.74/0.83  fof(f44,plain,(
% 1.74/0.83    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.74/0.83    inference(ennf_transformation,[],[f2])).
% 1.74/0.83  fof(f2,axiom,(
% 1.74/0.83    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.74/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.74/0.83  fof(f170,plain,(
% 1.74/0.83    spl4_1 | ~spl4_2),
% 1.74/0.83    inference(avatar_split_clause,[],[f159,f167,f163])).
% 1.74/0.83  fof(f159,plain,(
% 1.74/0.83    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 1.74/0.83    inference(resolution,[],[f108,f83])).
% 1.74/0.83  % SZS output end Proof for theBenchmark
% 1.74/0.83  % (10028)------------------------------
% 1.74/0.83  % (10028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.83  % (10028)Termination reason: Refutation
% 1.74/0.83  
% 1.74/0.83  % (10028)Memory used [KB]: 8059
% 1.74/0.83  % (10028)Time elapsed: 0.246 s
% 1.74/0.83  % (10028)------------------------------
% 1.74/0.83  % (10028)------------------------------
% 2.44/0.83  % (9863)Success in time 0.471 s
%------------------------------------------------------------------------------
