%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:25 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  238 ( 555 expanded)
%              Number of leaves         :   49 ( 204 expanded)
%              Depth                    :   21
%              Number of atoms          :  925 (1869 expanded)
%              Number of equality atoms :   54 ( 175 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f818,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f130,f135,f140,f145,f150,f175,f180,f194,f216,f224,f236,f241,f258,f261,f268,f292,f297,f302,f437,f452,f462,f520,f641,f759,f781,f806,f817])).

fof(f817,plain,
    ( ~ spl10_45
    | spl10_57 ),
    inference(avatar_contradiction_clause,[],[f816])).

fof(f816,plain,
    ( $false
    | ~ spl10_45
    | spl10_57 ),
    inference(subsumption_resolution,[],[f815,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f815,plain,
    ( ~ r1_tarski(k1_xboole_0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ spl10_45
    | spl10_57 ),
    inference(forward_demodulation,[],[f814,f640])).

fof(f640,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f638])).

fof(f638,plain,
    ( spl10_45
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f814,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | spl10_57 ),
    inference(subsumption_resolution,[],[f813,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f813,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | spl10_57 ),
    inference(superposition,[],[f805,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f805,plain,
    ( ~ r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | spl10_57 ),
    inference(avatar_component_clause,[],[f803])).

fof(f803,plain,
    ( spl10_57
  <=> r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f806,plain,
    ( ~ spl10_57
    | spl10_55 ),
    inference(avatar_split_clause,[],[f789,f778,f803])).

fof(f778,plain,
    ( spl10_55
  <=> r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f789,plain,
    ( ~ r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | spl10_55 ),
    inference(subsumption_resolution,[],[f788,f68])).

fof(f788,plain,
    ( ~ r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | spl10_55 ),
    inference(superposition,[],[f780,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f780,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | spl10_55 ),
    inference(avatar_component_clause,[],[f778])).

fof(f781,plain,
    ( ~ spl10_55
    | ~ spl10_18
    | spl10_36
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f763,f538,f517,f265,f778])).

fof(f265,plain,
    ( spl10_18
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f517,plain,
    ( spl10_36
  <=> r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK7(sK0,sK1,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK7(sK0,sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f538,plain,
    ( spl10_38
  <=> r1_tarski(sK7(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f763,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ spl10_18
    | spl10_36
    | ~ spl10_38 ),
    inference(backward_demodulation,[],[f519,f761])).

fof(f761,plain,
    ( k1_xboole_0 = sK7(sK0,sK1,k1_xboole_0)
    | ~ spl10_18
    | ~ spl10_38 ),
    inference(resolution,[],[f539,f393])).

fof(f393,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl10_18 ),
    inference(resolution,[],[f335,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f335,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X3 )
    | ~ spl10_18 ),
    inference(resolution,[],[f287,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f287,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f281,f119])).

fof(f119,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f281,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f269,f270])).

fof(f270,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl10_18 ),
    inference(resolution,[],[f267,f81])).

fof(f267,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f265])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
        | v1_xboole_0(X0) )
    | ~ spl10_18 ),
    inference(resolution,[],[f267,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f539,plain,
    ( r1_tarski(sK7(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f538])).

fof(f519,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK7(sK0,sK1,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK7(sK0,sK1,k1_xboole_0))))
    | spl10_36 ),
    inference(avatar_component_clause,[],[f517])).

fof(f759,plain,
    ( ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_21
    | ~ spl10_26
    | spl10_28
    | ~ spl10_30
    | spl10_38 ),
    inference(avatar_contradiction_clause,[],[f758])).

fof(f758,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_21
    | ~ spl10_26
    | spl10_28
    | ~ spl10_30
    | spl10_38 ),
    inference(subsumption_resolution,[],[f547,f757])).

fof(f757,plain,
    ( m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_21
    | ~ spl10_26
    | spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f756,f451])).

fof(f451,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl10_28 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl10_28
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f756,plain,
    ( m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f751,f139])).

fof(f139,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl10_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f751,plain,
    ( m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f749,f149])).

fof(f149,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl10_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f749,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_30 ),
    inference(resolution,[],[f636,f461])).

fof(f461,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl10_30
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f636,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(sK7(X0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_21
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f635,f68])).

fof(f635,plain,
    ( ! [X0] :
        ( m1_subset_1(sK7(X0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_21
    | ~ spl10_26 ),
    inference(resolution,[],[f321,f436])).

fof(f436,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl10_26
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f321,plain,
    ( ! [X8,X9] :
        ( ~ v1_funct_1(X9)
        | m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0)
        | ~ v2_pre_topc(X8)
        | v5_pre_topc(X9,X8,sK1) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_21 ),
    inference(forward_demodulation,[],[f320,f119])).

fof(f320,plain,
    ( ! [X8,X9] :
        ( m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),k1_xboole_0)))
        | ~ v2_pre_topc(X8)
        | v5_pre_topc(X9,X8,sK1) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f319,f134])).

fof(f134,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl10_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f319,plain,
    ( ! [X8,X9] :
        ( m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),k1_xboole_0)))
        | ~ v2_pre_topc(X8)
        | v5_pre_topc(X9,X8,sK1) )
    | ~ spl10_2
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f308,f129])).

fof(f129,plain,
    ( v2_pre_topc(sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl10_2
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f308,plain,
    ( ! [X8,X9] :
        ( m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),k1_xboole_0)))
        | ~ v2_pre_topc(X8)
        | v5_pre_topc(X9,X8,sK1) )
    | ~ spl10_21 ),
    inference(superposition,[],[f91,f301])).

fof(f301,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl10_21
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).

fof(f547,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl10_38 ),
    inference(resolution,[],[f540,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f540,plain,
    ( ~ r1_tarski(sK7(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | spl10_38 ),
    inference(avatar_component_clause,[],[f538])).

fof(f641,plain,
    ( spl10_45
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f634,f265,f638])).

fof(f634,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f632,f96])).

fof(f96,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

fof(f632,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl10_18 ),
    inference(superposition,[],[f478,f119])).

fof(f478,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(k2_zfmisc_1(X0,X1),k1_xboole_0)
        | k1_xboole_0 = k1_relat_1(k2_zfmisc_1(X0,X1)) )
    | ~ spl10_18 ),
    inference(resolution,[],[f465,f95])).

fof(f95,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f465,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0) )
    | ~ spl10_18 ),
    inference(resolution,[],[f393,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f520,plain,
    ( ~ spl10_36
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f406,f289,f265,f191,f177,f172,f147,f142,f137,f132,f127,f122,f517])).

fof(f122,plain,
    ( spl10_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f142,plain,
    ( spl10_5
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f172,plain,
    ( spl10_7
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f177,plain,
    ( spl10_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f191,plain,
    ( spl10_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f289,plain,
    ( spl10_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f406,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK7(sK0,sK1,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK7(sK0,sK1,k1_xboole_0))))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(backward_demodulation,[],[f276,f396])).

fof(f396,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(resolution,[],[f335,f291])).

fof(f291,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f289])).

fof(f276,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2))))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_11
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f231,f270])).

fof(f231,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2))))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f230,f174])).

fof(f174,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f172])).

fof(f230,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f229,f193])).

fof(f193,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f191])).

fof(f229,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f228,f129])).

fof(f228,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2))))
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f227,f134])).

fof(f227,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2))))
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(resolution,[],[f219,f179])).

fof(f179,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f177])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK7(sK0,X0,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,k2_pre_topc(X0,sK7(sK0,X0,sK2))))
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v5_pre_topc(sK2,sK0,X0) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(resolution,[],[f200,f124])).

fof(f124,plain,
    ( v1_funct_1(sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f199,f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f198,f139])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f196,f149])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1))))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(superposition,[],[f92,f170])).

fof(f170,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f169,f166])).

fof(f166,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f165,f139])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f162,f149])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f144,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(f144,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f142])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl10_6 ),
    inference(resolution,[],[f149,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f462,plain,
    ( spl10_30
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f409,f294,f289,f265,f459])).

fof(f294,plain,
    ( spl10_20
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f409,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_20 ),
    inference(backward_demodulation,[],[f296,f396])).

fof(f296,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f294])).

fof(f452,plain,
    ( ~ spl10_28
    | spl10_7
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f403,f289,f265,f172,f449])).

fof(f403,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl10_7
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(backward_demodulation,[],[f174,f396])).

fof(f437,plain,
    ( spl10_26
    | ~ spl10_1
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f399,f289,f265,f122,f434])).

fof(f399,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl10_1
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(backward_demodulation,[],[f124,f396])).

fof(f302,plain,
    ( spl10_21
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f270,f265,f299])).

fof(f297,plain,
    ( spl10_20
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f273,f265,f177,f294])).

fof(f273,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f179,f270])).

fof(f292,plain,
    ( spl10_19
    | ~ spl10_11
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f282,f265,f191,f289])).

fof(f282,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_11
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f274,f119])).

fof(f274,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl10_11
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f193,f270])).

fof(f268,plain,
    ( spl10_18
    | ~ spl10_16
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f263,f255,f251,f265])).

fof(f251,plain,
    ( spl10_16
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f255,plain,
    ( spl10_17
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f263,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_16
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f262,f256])).

fof(f256,plain,
    ( l1_struct_0(sK1)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f255])).

fof(f262,plain,
    ( ~ l1_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_16 ),
    inference(resolution,[],[f253,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f253,plain,
    ( v2_struct_0(sK1)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f251])).

fof(f261,plain,
    ( ~ spl10_3
    | spl10_17 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl10_3
    | spl10_17 ),
    inference(subsumption_resolution,[],[f259,f134])).

fof(f259,plain,
    ( ~ l1_pre_topc(sK1)
    | spl10_17 ),
    inference(resolution,[],[f257,f69])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f257,plain,
    ( ~ l1_struct_0(sK1)
    | spl10_17 ),
    inference(avatar_component_clause,[],[f255])).

fof(f258,plain,
    ( spl10_16
    | ~ spl10_17
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f247,f213,f255,f251])).

fof(f213,plain,
    ( spl10_13
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f247,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f242,f66])).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f242,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_13 ),
    inference(superposition,[],[f82,f215])).

fof(f215,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f213])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f241,plain,
    ( ~ spl10_11
    | spl10_15 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl10_11
    | spl10_15 ),
    inference(subsumption_resolution,[],[f237,f193])).

fof(f237,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl10_15 ),
    inference(resolution,[],[f235,f116])).

fof(f235,plain,
    ( ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl10_15 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl10_15
  <=> m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f236,plain,
    ( ~ spl10_15
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_14 ),
    inference(avatar_split_clause,[],[f226,f221,f147,f142,f137,f233])).

fof(f221,plain,
    ( spl10_14
  <=> v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f226,plain,
    ( ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_14 ),
    inference(resolution,[],[f223,f168])).

fof(f168,plain,
    ( ! [X1] :
        ( v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f167,f139])).

fof(f167,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X1,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f163,f149])).

fof(f163,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X1,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f144,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f223,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f221])).

fof(f224,plain,
    ( ~ spl10_14
    | spl10_12 ),
    inference(avatar_split_clause,[],[f218,f209,f221])).

fof(f209,plain,
    ( spl10_12
  <=> sP3(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f218,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)
    | spl10_12 ),
    inference(resolution,[],[f211,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

fof(f211,plain,
    ( ~ sP3(sK2,sK1,sK0)
    | spl10_12 ),
    inference(avatar_component_clause,[],[f209])).

fof(f216,plain,
    ( ~ spl10_12
    | spl10_13
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f207,f191,f177,f172,f147,f132,f122,f213,f209])).

fof(f207,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ sP3(sK2,sK1,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f206,f174])).

fof(f206,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ sP3(sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f205,f193])).

fof(f205,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ sP3(sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f204,f134])).

fof(f204,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ sP3(sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f203,f149])).

fof(f203,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ sP3(sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_8 ),
    inference(resolution,[],[f152,f179])).

fof(f152,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X4),u1_struct_0(X3))
        | ~ l1_pre_topc(X4)
        | ~ l1_pre_topc(X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
        | k1_xboole_0 = k2_struct_0(X3)
        | ~ sP3(sK2,X3,X4)
        | v5_pre_topc(sK2,X4,X3) )
    | ~ spl10_1 ),
    inference(resolution,[],[f124,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ sP3(X2,X1,X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f194,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f59,f191])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tex_2)).

fof(f180,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f58,f177])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f175,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f60,f172])).

fof(f60,plain,(
    ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f150,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f65,f147])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f145,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f64,f142])).

fof(f64,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f140,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f63,f137])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f135,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f62,f132])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f130,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f61,f127])).

fof(f61,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f125,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f57,f122])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:09:04 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.50  % (21516)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (21532)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (21524)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (21504)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (21504)Refutation not found, incomplete strategy% (21504)------------------------------
% 0.19/0.53  % (21504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (21504)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (21504)Memory used [KB]: 1663
% 0.19/0.53  % (21504)Time elapsed: 0.002 s
% 0.19/0.53  % (21504)------------------------------
% 0.19/0.53  % (21504)------------------------------
% 0.19/0.54  % (21509)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.54  % (21505)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.54  % (21511)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.54  % (21528)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.54  % (21531)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.54  % (21519)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.54  % (21506)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.54  % (21508)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.55  % (21513)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.55  % (21533)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.55  % (21513)Refutation not found, incomplete strategy% (21513)------------------------------
% 0.19/0.55  % (21513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (21513)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (21513)Memory used [KB]: 10618
% 0.19/0.55  % (21513)Time elapsed: 0.002 s
% 0.19/0.55  % (21513)------------------------------
% 0.19/0.55  % (21513)------------------------------
% 0.19/0.55  % (21526)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.55  % (21520)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.55  % (21523)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.55  % (21514)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.55  % (21515)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.55  % (21512)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.56  % (21510)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.56  % (21514)Refutation not found, incomplete strategy% (21514)------------------------------
% 0.19/0.56  % (21514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (21514)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (21514)Memory used [KB]: 10618
% 0.19/0.56  % (21514)Time elapsed: 0.151 s
% 0.19/0.56  % (21514)------------------------------
% 0.19/0.56  % (21514)------------------------------
% 0.19/0.56  % (21529)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.56  % (21521)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.56  % (21518)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.56  % (21521)Refutation not found, incomplete strategy% (21521)------------------------------
% 0.19/0.56  % (21521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (21521)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (21521)Memory used [KB]: 10618
% 0.19/0.56  % (21521)Time elapsed: 0.165 s
% 0.19/0.56  % (21521)------------------------------
% 0.19/0.56  % (21521)------------------------------
% 0.19/0.56  % (21507)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.56  % (21517)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.57  % (21512)Refutation not found, incomplete strategy% (21512)------------------------------
% 0.19/0.57  % (21512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (21515)Refutation not found, incomplete strategy% (21515)------------------------------
% 0.19/0.57  % (21515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (21515)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.57  
% 0.19/0.57  % (21515)Memory used [KB]: 10618
% 0.19/0.57  % (21515)Time elapsed: 0.172 s
% 0.19/0.57  % (21515)------------------------------
% 0.19/0.57  % (21515)------------------------------
% 0.19/0.57  % (21506)Refutation not found, incomplete strategy% (21506)------------------------------
% 0.19/0.57  % (21506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (21506)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.57  
% 0.19/0.57  % (21506)Memory used [KB]: 11129
% 0.19/0.57  % (21506)Time elapsed: 0.166 s
% 0.19/0.57  % (21506)------------------------------
% 0.19/0.57  % (21506)------------------------------
% 0.19/0.57  % (21512)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.57  
% 0.19/0.57  % (21512)Memory used [KB]: 10874
% 0.19/0.57  % (21512)Time elapsed: 0.145 s
% 0.19/0.57  % (21512)------------------------------
% 0.19/0.57  % (21512)------------------------------
% 0.19/0.57  % (21526)Refutation not found, incomplete strategy% (21526)------------------------------
% 0.19/0.57  % (21526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (21526)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.57  
% 0.19/0.57  % (21526)Memory used [KB]: 10874
% 0.19/0.57  % (21526)Time elapsed: 0.137 s
% 0.19/0.57  % (21526)------------------------------
% 0.19/0.57  % (21526)------------------------------
% 0.19/0.57  % (21527)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.58  % (21525)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.58  % (21522)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.58  % (21530)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.96/0.59  % (21524)Refutation found. Thanks to Tanya!
% 1.96/0.59  % SZS status Theorem for theBenchmark
% 1.96/0.59  % SZS output start Proof for theBenchmark
% 1.96/0.59  fof(f818,plain,(
% 1.96/0.59    $false),
% 1.96/0.59    inference(avatar_sat_refutation,[],[f125,f130,f135,f140,f145,f150,f175,f180,f194,f216,f224,f236,f241,f258,f261,f268,f292,f297,f302,f437,f452,f462,f520,f641,f759,f781,f806,f817])).
% 1.96/0.59  fof(f817,plain,(
% 1.96/0.59    ~spl10_45 | spl10_57),
% 1.96/0.59    inference(avatar_contradiction_clause,[],[f816])).
% 1.96/0.59  fof(f816,plain,(
% 1.96/0.59    $false | (~spl10_45 | spl10_57)),
% 1.96/0.59    inference(subsumption_resolution,[],[f815,f67])).
% 1.96/0.59  fof(f67,plain,(
% 1.96/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f6])).
% 1.96/0.59  fof(f6,axiom,(
% 1.96/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.96/0.59  fof(f815,plain,(
% 1.96/0.59    ~r1_tarski(k1_xboole_0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | (~spl10_45 | spl10_57)),
% 1.96/0.59    inference(forward_demodulation,[],[f814,f640])).
% 1.96/0.59  fof(f640,plain,(
% 1.96/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl10_45),
% 1.96/0.59    inference(avatar_component_clause,[],[f638])).
% 1.96/0.59  fof(f638,plain,(
% 1.96/0.59    spl10_45 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).
% 1.96/0.59  fof(f814,plain,(
% 1.96/0.59    ~r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | spl10_57),
% 1.96/0.59    inference(subsumption_resolution,[],[f813,f68])).
% 1.96/0.59  fof(f68,plain,(
% 1.96/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.96/0.59    inference(cnf_transformation,[],[f8])).
% 1.96/0.59  fof(f8,axiom,(
% 1.96/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.96/0.59  fof(f813,plain,(
% 1.96/0.59    ~r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | spl10_57),
% 1.96/0.59    inference(superposition,[],[f805,f112])).
% 1.96/0.59  fof(f112,plain,(
% 1.96/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/0.59    inference(cnf_transformation,[],[f52])).
% 1.96/0.59  fof(f52,plain,(
% 1.96/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.59    inference(ennf_transformation,[],[f16])).
% 1.96/0.59  fof(f16,axiom,(
% 1.96/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.96/0.59  fof(f805,plain,(
% 1.96/0.59    ~r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | spl10_57),
% 1.96/0.59    inference(avatar_component_clause,[],[f803])).
% 1.96/0.59  fof(f803,plain,(
% 1.96/0.59    spl10_57 <=> r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).
% 1.96/0.59  fof(f806,plain,(
% 1.96/0.59    ~spl10_57 | spl10_55),
% 1.96/0.59    inference(avatar_split_clause,[],[f789,f778,f803])).
% 1.96/0.59  fof(f778,plain,(
% 1.96/0.59    spl10_55 <=> r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).
% 1.96/0.59  fof(f789,plain,(
% 1.96/0.59    ~r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | spl10_55),
% 1.96/0.59    inference(subsumption_resolution,[],[f788,f68])).
% 1.96/0.59  fof(f788,plain,(
% 1.96/0.59    ~r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | spl10_55),
% 1.96/0.59    inference(superposition,[],[f780,f114])).
% 1.96/0.59  fof(f114,plain,(
% 1.96/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/0.59    inference(cnf_transformation,[],[f53])).
% 1.96/0.59  fof(f53,plain,(
% 1.96/0.59    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.59    inference(ennf_transformation,[],[f17])).
% 1.96/0.59  fof(f17,axiom,(
% 1.96/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 1.96/0.59  fof(f780,plain,(
% 1.96/0.59    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | spl10_55),
% 1.96/0.59    inference(avatar_component_clause,[],[f778])).
% 1.96/0.59  fof(f781,plain,(
% 1.96/0.59    ~spl10_55 | ~spl10_18 | spl10_36 | ~spl10_38),
% 1.96/0.59    inference(avatar_split_clause,[],[f763,f538,f517,f265,f778])).
% 1.96/0.59  fof(f265,plain,(
% 1.96/0.59    spl10_18 <=> v1_xboole_0(u1_struct_0(sK1))),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 1.96/0.59  fof(f517,plain,(
% 1.96/0.59    spl10_36 <=> r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK7(sK0,sK1,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK7(sK0,sK1,k1_xboole_0))))),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 1.96/0.59  fof(f538,plain,(
% 1.96/0.59    spl10_38 <=> r1_tarski(sK7(sK0,sK1,k1_xboole_0),k1_xboole_0)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 1.96/0.59  fof(f763,plain,(
% 1.96/0.59    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | (~spl10_18 | spl10_36 | ~spl10_38)),
% 1.96/0.59    inference(backward_demodulation,[],[f519,f761])).
% 1.96/0.59  fof(f761,plain,(
% 1.96/0.59    k1_xboole_0 = sK7(sK0,sK1,k1_xboole_0) | (~spl10_18 | ~spl10_38)),
% 1.96/0.59    inference(resolution,[],[f539,f393])).
% 1.96/0.59  fof(f393,plain,(
% 1.96/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl10_18),
% 1.96/0.59    inference(resolution,[],[f335,f107])).
% 1.96/0.59  fof(f107,plain,(
% 1.96/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f9])).
% 1.96/0.59  fof(f9,axiom,(
% 1.96/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.96/0.59  fof(f335,plain,(
% 1.96/0.59    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X3) ) | ~spl10_18),
% 1.96/0.59    inference(resolution,[],[f287,f81])).
% 1.96/0.59  fof(f81,plain,(
% 1.96/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.96/0.59    inference(cnf_transformation,[],[f38])).
% 1.96/0.59  fof(f38,plain,(
% 1.96/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.96/0.59    inference(ennf_transformation,[],[f4])).
% 1.96/0.59  fof(f4,axiom,(
% 1.96/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.96/0.59  fof(f287,plain,(
% 1.96/0.59    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl10_18),
% 1.96/0.59    inference(forward_demodulation,[],[f281,f119])).
% 1.96/0.59  fof(f119,plain,(
% 1.96/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.96/0.59    inference(equality_resolution,[],[f111])).
% 1.96/0.59  fof(f111,plain,(
% 1.96/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f7])).
% 1.96/0.59  fof(f7,axiom,(
% 1.96/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.96/0.59  fof(f281,plain,(
% 1.96/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) ) | ~spl10_18),
% 1.96/0.59    inference(backward_demodulation,[],[f269,f270])).
% 1.96/0.59  fof(f270,plain,(
% 1.96/0.59    k1_xboole_0 = u1_struct_0(sK1) | ~spl10_18),
% 1.96/0.59    inference(resolution,[],[f267,f81])).
% 1.96/0.59  fof(f267,plain,(
% 1.96/0.59    v1_xboole_0(u1_struct_0(sK1)) | ~spl10_18),
% 1.96/0.59    inference(avatar_component_clause,[],[f265])).
% 1.96/0.59  fof(f269,plain,(
% 1.96/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) | v1_xboole_0(X0)) ) | ~spl10_18),
% 1.96/0.59    inference(resolution,[],[f267,f100])).
% 1.96/0.59  fof(f100,plain,(
% 1.96/0.59    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f50])).
% 1.96/0.59  fof(f50,plain,(
% 1.96/0.59    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.96/0.59    inference(ennf_transformation,[],[f14])).
% 1.96/0.59  fof(f14,axiom,(
% 1.96/0.59    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.96/0.59  fof(f539,plain,(
% 1.96/0.59    r1_tarski(sK7(sK0,sK1,k1_xboole_0),k1_xboole_0) | ~spl10_38),
% 1.96/0.59    inference(avatar_component_clause,[],[f538])).
% 1.96/0.59  fof(f519,plain,(
% 1.96/0.59    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK7(sK0,sK1,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK7(sK0,sK1,k1_xboole_0)))) | spl10_36),
% 1.96/0.59    inference(avatar_component_clause,[],[f517])).
% 1.96/0.59  fof(f759,plain,(
% 1.96/0.59    ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_6 | ~spl10_21 | ~spl10_26 | spl10_28 | ~spl10_30 | spl10_38),
% 1.96/0.59    inference(avatar_contradiction_clause,[],[f758])).
% 1.96/0.59  fof(f758,plain,(
% 1.96/0.59    $false | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_6 | ~spl10_21 | ~spl10_26 | spl10_28 | ~spl10_30 | spl10_38)),
% 1.96/0.59    inference(subsumption_resolution,[],[f547,f757])).
% 1.96/0.59  fof(f757,plain,(
% 1.96/0.59    m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_6 | ~spl10_21 | ~spl10_26 | spl10_28 | ~spl10_30)),
% 1.96/0.59    inference(subsumption_resolution,[],[f756,f451])).
% 1.96/0.59  fof(f451,plain,(
% 1.96/0.59    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl10_28),
% 1.96/0.59    inference(avatar_component_clause,[],[f449])).
% 1.96/0.59  fof(f449,plain,(
% 1.96/0.59    spl10_28 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 1.96/0.59  fof(f756,plain,(
% 1.96/0.59    m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_6 | ~spl10_21 | ~spl10_26 | ~spl10_30)),
% 1.96/0.59    inference(subsumption_resolution,[],[f751,f139])).
% 1.96/0.59  fof(f139,plain,(
% 1.96/0.59    v2_pre_topc(sK0) | ~spl10_4),
% 1.96/0.59    inference(avatar_component_clause,[],[f137])).
% 1.96/0.59  fof(f137,plain,(
% 1.96/0.59    spl10_4 <=> v2_pre_topc(sK0)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.96/0.59  fof(f751,plain,(
% 1.96/0.59    m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl10_2 | ~spl10_3 | ~spl10_6 | ~spl10_21 | ~spl10_26 | ~spl10_30)),
% 1.96/0.59    inference(subsumption_resolution,[],[f749,f149])).
% 1.96/0.59  fof(f149,plain,(
% 1.96/0.59    l1_pre_topc(sK0) | ~spl10_6),
% 1.96/0.59    inference(avatar_component_clause,[],[f147])).
% 1.96/0.59  fof(f147,plain,(
% 1.96/0.59    spl10_6 <=> l1_pre_topc(sK0)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.96/0.59  fof(f749,plain,(
% 1.96/0.59    ~l1_pre_topc(sK0) | m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl10_2 | ~spl10_3 | ~spl10_21 | ~spl10_26 | ~spl10_30)),
% 1.96/0.59    inference(resolution,[],[f636,f461])).
% 1.96/0.59  fof(f461,plain,(
% 1.96/0.59    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~spl10_30),
% 1.96/0.59    inference(avatar_component_clause,[],[f459])).
% 1.96/0.59  fof(f459,plain,(
% 1.96/0.59    spl10_30 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 1.96/0.59  fof(f636,plain,(
% 1.96/0.59    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~l1_pre_topc(X0) | m1_subset_1(sK7(X0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(X0) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | (~spl10_2 | ~spl10_3 | ~spl10_21 | ~spl10_26)),
% 1.96/0.59    inference(subsumption_resolution,[],[f635,f68])).
% 1.96/0.59  fof(f635,plain,(
% 1.96/0.59    ( ! [X0] : (m1_subset_1(sK7(X0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v2_pre_topc(X0) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | (~spl10_2 | ~spl10_3 | ~spl10_21 | ~spl10_26)),
% 1.96/0.59    inference(resolution,[],[f321,f436])).
% 1.96/0.59  fof(f436,plain,(
% 1.96/0.59    v1_funct_1(k1_xboole_0) | ~spl10_26),
% 1.96/0.59    inference(avatar_component_clause,[],[f434])).
% 1.96/0.59  fof(f434,plain,(
% 1.96/0.59    spl10_26 <=> v1_funct_1(k1_xboole_0)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 1.96/0.59  fof(f321,plain,(
% 1.96/0.59    ( ! [X8,X9] : (~v1_funct_1(X9) | m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(X8) | ~m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0) | ~v2_pre_topc(X8) | v5_pre_topc(X9,X8,sK1)) ) | (~spl10_2 | ~spl10_3 | ~spl10_21)),
% 1.96/0.59    inference(forward_demodulation,[],[f320,f119])).
% 1.96/0.59  fof(f320,plain,(
% 1.96/0.59    ( ! [X8,X9] : (m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(X8) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),k1_xboole_0))) | ~v2_pre_topc(X8) | v5_pre_topc(X9,X8,sK1)) ) | (~spl10_2 | ~spl10_3 | ~spl10_21)),
% 1.96/0.59    inference(subsumption_resolution,[],[f319,f134])).
% 1.96/0.59  fof(f134,plain,(
% 1.96/0.59    l1_pre_topc(sK1) | ~spl10_3),
% 1.96/0.59    inference(avatar_component_clause,[],[f132])).
% 1.96/0.59  fof(f132,plain,(
% 1.96/0.59    spl10_3 <=> l1_pre_topc(sK1)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.96/0.59  fof(f319,plain,(
% 1.96/0.59    ( ! [X8,X9] : (m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(X8) | ~l1_pre_topc(sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),k1_xboole_0))) | ~v2_pre_topc(X8) | v5_pre_topc(X9,X8,sK1)) ) | (~spl10_2 | ~spl10_21)),
% 1.96/0.59    inference(subsumption_resolution,[],[f308,f129])).
% 1.96/0.59  fof(f129,plain,(
% 1.96/0.59    v2_pre_topc(sK1) | ~spl10_2),
% 1.96/0.59    inference(avatar_component_clause,[],[f127])).
% 1.96/0.59  fof(f127,plain,(
% 1.96/0.59    spl10_2 <=> v2_pre_topc(sK1)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.96/0.59  fof(f308,plain,(
% 1.96/0.59    ( ! [X8,X9] : (m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(X8) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),k1_xboole_0))) | ~v2_pre_topc(X8) | v5_pre_topc(X9,X8,sK1)) ) | ~spl10_21),
% 1.96/0.59    inference(superposition,[],[f91,f301])).
% 1.96/0.59  fof(f301,plain,(
% 1.96/0.59    k1_xboole_0 = u1_struct_0(sK1) | ~spl10_21),
% 1.96/0.59    inference(avatar_component_clause,[],[f299])).
% 1.96/0.59  fof(f299,plain,(
% 1.96/0.59    spl10_21 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 1.96/0.59  fof(f91,plain,(
% 1.96/0.59    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f48])).
% 1.96/0.59  fof(f48,plain,(
% 1.96/0.59    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.96/0.59    inference(flattening,[],[f47])).
% 1.96/0.59  fof(f47,plain,(
% 1.96/0.59    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.96/0.59    inference(ennf_transformation,[],[f23])).
% 1.96/0.59  fof(f23,axiom,(
% 1.96/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).
% 1.96/0.59  fof(f547,plain,(
% 1.96/0.59    ~m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | spl10_38),
% 1.96/0.59    inference(resolution,[],[f540,f108])).
% 1.96/0.59  fof(f108,plain,(
% 1.96/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.96/0.59    inference(cnf_transformation,[],[f9])).
% 1.96/0.59  fof(f540,plain,(
% 1.96/0.59    ~r1_tarski(sK7(sK0,sK1,k1_xboole_0),k1_xboole_0) | spl10_38),
% 1.96/0.59    inference(avatar_component_clause,[],[f538])).
% 1.96/0.59  fof(f641,plain,(
% 1.96/0.59    spl10_45 | ~spl10_18),
% 1.96/0.59    inference(avatar_split_clause,[],[f634,f265,f638])).
% 1.96/0.59  fof(f634,plain,(
% 1.96/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl10_18),
% 1.96/0.59    inference(subsumption_resolution,[],[f632,f96])).
% 1.96/0.59  fof(f96,plain,(
% 1.96/0.59    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f13])).
% 1.96/0.59  fof(f13,axiom,(
% 1.96/0.59    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).
% 1.96/0.59  fof(f632,plain,(
% 1.96/0.59    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl10_18),
% 1.96/0.59    inference(superposition,[],[f478,f119])).
% 1.96/0.59  fof(f478,plain,(
% 1.96/0.59    ( ! [X0,X1] : (~v4_relat_1(k2_zfmisc_1(X0,X1),k1_xboole_0) | k1_xboole_0 = k1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl10_18),
% 1.96/0.59    inference(resolution,[],[f465,f95])).
% 1.96/0.59  fof(f95,plain,(
% 1.96/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.96/0.59    inference(cnf_transformation,[],[f12])).
% 1.96/0.59  fof(f12,axiom,(
% 1.96/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.96/0.59  fof(f465,plain,(
% 1.96/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v4_relat_1(X0,k1_xboole_0)) ) | ~spl10_18),
% 1.96/0.59    inference(resolution,[],[f393,f99])).
% 1.96/0.59  fof(f99,plain,(
% 1.96/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f49])).
% 1.96/0.59  fof(f49,plain,(
% 1.96/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.96/0.59    inference(ennf_transformation,[],[f11])).
% 1.96/0.59  fof(f11,axiom,(
% 1.96/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.96/0.59  fof(f520,plain,(
% 1.96/0.59    ~spl10_36 | ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_11 | ~spl10_18 | ~spl10_19),
% 1.96/0.59    inference(avatar_split_clause,[],[f406,f289,f265,f191,f177,f172,f147,f142,f137,f132,f127,f122,f517])).
% 1.96/0.59  fof(f122,plain,(
% 1.96/0.59    spl10_1 <=> v1_funct_1(sK2)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.96/0.59  fof(f142,plain,(
% 1.96/0.59    spl10_5 <=> v1_tdlat_3(sK0)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.96/0.59  fof(f172,plain,(
% 1.96/0.59    spl10_7 <=> v5_pre_topc(sK2,sK0,sK1)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.96/0.59  fof(f177,plain,(
% 1.96/0.59    spl10_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.96/0.59  fof(f191,plain,(
% 1.96/0.59    spl10_11 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.96/0.59  fof(f289,plain,(
% 1.96/0.59    spl10_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 1.96/0.59  fof(f406,plain,(
% 1.96/0.59    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK7(sK0,sK1,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK7(sK0,sK1,k1_xboole_0)))) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_11 | ~spl10_18 | ~spl10_19)),
% 1.96/0.59    inference(backward_demodulation,[],[f276,f396])).
% 1.96/0.59  fof(f396,plain,(
% 1.96/0.59    k1_xboole_0 = sK2 | (~spl10_18 | ~spl10_19)),
% 1.96/0.59    inference(resolution,[],[f335,f291])).
% 1.96/0.59  fof(f291,plain,(
% 1.96/0.59    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl10_19),
% 1.96/0.59    inference(avatar_component_clause,[],[f289])).
% 1.96/0.59  fof(f276,plain,(
% 1.96/0.59    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2)))) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_11 | ~spl10_18)),
% 1.96/0.59    inference(backward_demodulation,[],[f231,f270])).
% 1.96/0.59  fof(f231,plain,(
% 1.96/0.59    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2)))) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_11)),
% 1.96/0.59    inference(subsumption_resolution,[],[f230,f174])).
% 1.96/0.59  fof(f174,plain,(
% 1.96/0.59    ~v5_pre_topc(sK2,sK0,sK1) | spl10_7),
% 1.96/0.59    inference(avatar_component_clause,[],[f172])).
% 1.96/0.59  fof(f230,plain,(
% 1.96/0.59    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2)))) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_8 | ~spl10_11)),
% 1.96/0.59    inference(subsumption_resolution,[],[f229,f193])).
% 1.96/0.59  fof(f193,plain,(
% 1.96/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl10_11),
% 1.96/0.59    inference(avatar_component_clause,[],[f191])).
% 1.96/0.59  fof(f229,plain,(
% 1.96/0.59    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_8)),
% 1.96/0.59    inference(subsumption_resolution,[],[f228,f129])).
% 1.96/0.59  fof(f228,plain,(
% 1.96/0.59    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2)))) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_8)),
% 1.96/0.59    inference(subsumption_resolution,[],[f227,f134])).
% 1.96/0.59  fof(f227,plain,(
% 1.96/0.59    ~l1_pre_topc(sK1) | ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2)))) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_8)),
% 1.96/0.59    inference(resolution,[],[f219,f179])).
% 1.96/0.59  fof(f179,plain,(
% 1.96/0.59    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl10_8),
% 1.96/0.59    inference(avatar_component_clause,[],[f177])).
% 1.96/0.59  fof(f219,plain,(
% 1.96/0.59    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK7(sK0,X0,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,k2_pre_topc(X0,sK7(sK0,X0,sK2)))) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v5_pre_topc(sK2,sK0,X0)) ) | (~spl10_1 | ~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.59    inference(resolution,[],[f200,f124])).
% 1.96/0.59  fof(f124,plain,(
% 1.96/0.59    v1_funct_1(sK2) | ~spl10_1),
% 1.96/0.59    inference(avatar_component_clause,[],[f122])).
% 1.96/0.59  fof(f200,plain,(
% 1.96/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0)) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.59    inference(subsumption_resolution,[],[f199,f116])).
% 1.96/0.59  fof(f116,plain,(
% 1.96/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/0.59    inference(cnf_transformation,[],[f56])).
% 1.96/0.59  fof(f56,plain,(
% 1.96/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.59    inference(ennf_transformation,[],[f15])).
% 1.96/0.59  fof(f15,axiom,(
% 1.96/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 1.96/0.59  fof(f199,plain,(
% 1.96/0.59    ( ! [X0,X1] : (~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.59    inference(subsumption_resolution,[],[f198,f139])).
% 1.96/0.59  fof(f198,plain,(
% 1.96/0.59    ( ! [X0,X1] : (~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.59    inference(subsumption_resolution,[],[f196,f149])).
% 1.96/0.59  fof(f196,plain,(
% 1.96/0.59    ( ! [X0,X1] : (~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.59    inference(superposition,[],[f92,f170])).
% 1.96/0.59  fof(f170,plain,(
% 1.96/0.59    ( ! [X0] : (k2_pre_topc(sK0,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.59    inference(subsumption_resolution,[],[f169,f166])).
% 1.96/0.59  fof(f166,plain,(
% 1.96/0.59    ( ! [X0] : (v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.59    inference(subsumption_resolution,[],[f165,f139])).
% 1.96/0.59  fof(f165,plain,(
% 1.96/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) ) | (~spl10_5 | ~spl10_6)),
% 1.96/0.59    inference(subsumption_resolution,[],[f162,f149])).
% 1.96/0.59  fof(f162,plain,(
% 1.96/0.59    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) ) | ~spl10_5),
% 1.96/0.59    inference(resolution,[],[f144,f87])).
% 1.96/0.59  fof(f87,plain,(
% 1.96/0.59    ( ! [X0,X1] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f46])).
% 1.96/0.59  fof(f46,plain,(
% 1.96/0.59    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.96/0.59    inference(flattening,[],[f45])).
% 1.96/0.59  fof(f45,plain,(
% 1.96/0.59    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.96/0.59    inference(ennf_transformation,[],[f26])).
% 1.96/0.59  fof(f26,axiom,(
% 1.96/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tdlat_3)).
% 1.96/0.59  fof(f144,plain,(
% 1.96/0.59    v1_tdlat_3(sK0) | ~spl10_5),
% 1.96/0.59    inference(avatar_component_clause,[],[f142])).
% 1.96/0.59  fof(f169,plain,(
% 1.96/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) ) | ~spl10_6),
% 1.96/0.59    inference(resolution,[],[f149,f80])).
% 1.96/0.59  fof(f80,plain,(
% 1.96/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.96/0.59    inference(cnf_transformation,[],[f37])).
% 1.96/0.59  fof(f37,plain,(
% 1.96/0.59    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.96/0.59    inference(flattening,[],[f36])).
% 1.96/0.59  fof(f36,plain,(
% 1.96/0.59    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.96/0.59    inference(ennf_transformation,[],[f21])).
% 1.96/0.59  fof(f21,axiom,(
% 1.96/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.96/0.59  fof(f92,plain,(
% 1.96/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f48])).
% 1.96/0.59  fof(f462,plain,(
% 1.96/0.59    spl10_30 | ~spl10_18 | ~spl10_19 | ~spl10_20),
% 1.96/0.59    inference(avatar_split_clause,[],[f409,f294,f289,f265,f459])).
% 1.96/0.59  fof(f294,plain,(
% 1.96/0.59    spl10_20 <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 1.96/0.59  fof(f409,plain,(
% 1.96/0.59    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl10_18 | ~spl10_19 | ~spl10_20)),
% 1.96/0.59    inference(backward_demodulation,[],[f296,f396])).
% 1.96/0.59  fof(f296,plain,(
% 1.96/0.59    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~spl10_20),
% 1.96/0.59    inference(avatar_component_clause,[],[f294])).
% 1.96/0.59  fof(f452,plain,(
% 1.96/0.59    ~spl10_28 | spl10_7 | ~spl10_18 | ~spl10_19),
% 1.96/0.59    inference(avatar_split_clause,[],[f403,f289,f265,f172,f449])).
% 1.96/0.59  fof(f403,plain,(
% 1.96/0.59    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl10_7 | ~spl10_18 | ~spl10_19)),
% 1.96/0.59    inference(backward_demodulation,[],[f174,f396])).
% 1.96/0.59  fof(f437,plain,(
% 1.96/0.59    spl10_26 | ~spl10_1 | ~spl10_18 | ~spl10_19),
% 1.96/0.59    inference(avatar_split_clause,[],[f399,f289,f265,f122,f434])).
% 1.96/0.59  fof(f399,plain,(
% 1.96/0.59    v1_funct_1(k1_xboole_0) | (~spl10_1 | ~spl10_18 | ~spl10_19)),
% 1.96/0.59    inference(backward_demodulation,[],[f124,f396])).
% 1.96/0.59  fof(f302,plain,(
% 1.96/0.59    spl10_21 | ~spl10_18),
% 1.96/0.59    inference(avatar_split_clause,[],[f270,f265,f299])).
% 1.96/0.59  fof(f297,plain,(
% 1.96/0.59    spl10_20 | ~spl10_8 | ~spl10_18),
% 1.96/0.59    inference(avatar_split_clause,[],[f273,f265,f177,f294])).
% 1.96/0.59  fof(f273,plain,(
% 1.96/0.59    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (~spl10_8 | ~spl10_18)),
% 1.96/0.59    inference(backward_demodulation,[],[f179,f270])).
% 1.96/0.59  fof(f292,plain,(
% 1.96/0.59    spl10_19 | ~spl10_11 | ~spl10_18),
% 1.96/0.59    inference(avatar_split_clause,[],[f282,f265,f191,f289])).
% 1.96/0.59  fof(f282,plain,(
% 1.96/0.59    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl10_11 | ~spl10_18)),
% 1.96/0.59    inference(forward_demodulation,[],[f274,f119])).
% 1.96/0.59  fof(f274,plain,(
% 1.96/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl10_11 | ~spl10_18)),
% 1.96/0.59    inference(backward_demodulation,[],[f193,f270])).
% 1.96/0.59  fof(f268,plain,(
% 1.96/0.59    spl10_18 | ~spl10_16 | ~spl10_17),
% 1.96/0.59    inference(avatar_split_clause,[],[f263,f255,f251,f265])).
% 1.96/0.59  fof(f251,plain,(
% 1.96/0.59    spl10_16 <=> v2_struct_0(sK1)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.96/0.59  fof(f255,plain,(
% 1.96/0.59    spl10_17 <=> l1_struct_0(sK1)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 1.96/0.59  fof(f263,plain,(
% 1.96/0.59    v1_xboole_0(u1_struct_0(sK1)) | (~spl10_16 | ~spl10_17)),
% 1.96/0.59    inference(subsumption_resolution,[],[f262,f256])).
% 1.96/0.59  fof(f256,plain,(
% 1.96/0.59    l1_struct_0(sK1) | ~spl10_17),
% 1.96/0.59    inference(avatar_component_clause,[],[f255])).
% 1.96/0.59  fof(f262,plain,(
% 1.96/0.59    ~l1_struct_0(sK1) | v1_xboole_0(u1_struct_0(sK1)) | ~spl10_16),
% 1.96/0.59    inference(resolution,[],[f253,f83])).
% 1.96/0.59  fof(f83,plain,(
% 1.96/0.59    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 1.96/0.59    inference(cnf_transformation,[],[f42])).
% 1.96/0.59  fof(f42,plain,(
% 1.96/0.59    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 1.96/0.59    inference(flattening,[],[f41])).
% 1.96/0.59  fof(f41,plain,(
% 1.96/0.59    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 1.96/0.59    inference(ennf_transformation,[],[f19])).
% 1.96/0.59  fof(f19,axiom,(
% 1.96/0.59    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).
% 1.96/0.59  fof(f253,plain,(
% 1.96/0.59    v2_struct_0(sK1) | ~spl10_16),
% 1.96/0.59    inference(avatar_component_clause,[],[f251])).
% 1.96/0.59  fof(f261,plain,(
% 1.96/0.59    ~spl10_3 | spl10_17),
% 1.96/0.59    inference(avatar_contradiction_clause,[],[f260])).
% 1.96/0.59  fof(f260,plain,(
% 1.96/0.59    $false | (~spl10_3 | spl10_17)),
% 1.96/0.59    inference(subsumption_resolution,[],[f259,f134])).
% 1.96/0.59  fof(f259,plain,(
% 1.96/0.59    ~l1_pre_topc(sK1) | spl10_17),
% 1.96/0.59    inference(resolution,[],[f257,f69])).
% 1.96/0.59  fof(f69,plain,(
% 1.96/0.59    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f31])).
% 1.96/0.59  fof(f31,plain,(
% 1.96/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.96/0.59    inference(ennf_transformation,[],[f18])).
% 1.96/0.59  fof(f18,axiom,(
% 1.96/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.96/0.59  fof(f257,plain,(
% 1.96/0.59    ~l1_struct_0(sK1) | spl10_17),
% 1.96/0.59    inference(avatar_component_clause,[],[f255])).
% 1.96/0.59  fof(f258,plain,(
% 1.96/0.59    spl10_16 | ~spl10_17 | ~spl10_13),
% 1.96/0.59    inference(avatar_split_clause,[],[f247,f213,f255,f251])).
% 1.96/0.59  fof(f213,plain,(
% 1.96/0.59    spl10_13 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 1.96/0.59  fof(f247,plain,(
% 1.96/0.59    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl10_13),
% 1.96/0.59    inference(subsumption_resolution,[],[f242,f66])).
% 1.96/0.59  fof(f66,plain,(
% 1.96/0.59    v1_xboole_0(k1_xboole_0)),
% 1.96/0.59    inference(cnf_transformation,[],[f3])).
% 1.96/0.59  fof(f3,axiom,(
% 1.96/0.59    v1_xboole_0(k1_xboole_0)),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.96/0.59  fof(f242,plain,(
% 1.96/0.59    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl10_13),
% 1.96/0.59    inference(superposition,[],[f82,f215])).
% 1.96/0.59  fof(f215,plain,(
% 1.96/0.59    k1_xboole_0 = k2_struct_0(sK1) | ~spl10_13),
% 1.96/0.59    inference(avatar_component_clause,[],[f213])).
% 1.96/0.59  fof(f82,plain,(
% 1.96/0.59    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f40])).
% 1.96/0.59  fof(f40,plain,(
% 1.96/0.59    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.96/0.59    inference(flattening,[],[f39])).
% 1.96/0.59  fof(f39,plain,(
% 1.96/0.59    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.96/0.59    inference(ennf_transformation,[],[f20])).
% 1.96/0.59  fof(f20,axiom,(
% 1.96/0.59    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.96/0.59  fof(f241,plain,(
% 1.96/0.59    ~spl10_11 | spl10_15),
% 1.96/0.59    inference(avatar_contradiction_clause,[],[f240])).
% 1.96/0.59  fof(f240,plain,(
% 1.96/0.59    $false | (~spl10_11 | spl10_15)),
% 1.96/0.59    inference(subsumption_resolution,[],[f237,f193])).
% 1.96/0.59  fof(f237,plain,(
% 1.96/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl10_15),
% 1.96/0.59    inference(resolution,[],[f235,f116])).
% 1.96/0.59  fof(f235,plain,(
% 1.96/0.59    ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl10_15),
% 1.96/0.59    inference(avatar_component_clause,[],[f233])).
% 1.96/0.59  fof(f233,plain,(
% 1.96/0.59    spl10_15 <=> m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 1.96/0.59  fof(f236,plain,(
% 1.96/0.59    ~spl10_15 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_14),
% 1.96/0.59    inference(avatar_split_clause,[],[f226,f221,f147,f142,f137,f233])).
% 1.96/0.59  fof(f221,plain,(
% 1.96/0.59    spl10_14 <=> v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 1.96/0.59  fof(f226,plain,(
% 1.96/0.59    ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_14)),
% 1.96/0.59    inference(resolution,[],[f223,f168])).
% 1.96/0.59  fof(f168,plain,(
% 1.96/0.59    ( ! [X1] : (v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.59    inference(subsumption_resolution,[],[f167,f139])).
% 1.96/0.59  fof(f167,plain,(
% 1.96/0.59    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0) | ~v2_pre_topc(sK0)) ) | (~spl10_5 | ~spl10_6)),
% 1.96/0.59    inference(subsumption_resolution,[],[f163,f149])).
% 1.96/0.59  fof(f163,plain,(
% 1.96/0.59    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0) | ~v2_pre_topc(sK0)) ) | ~spl10_5),
% 1.96/0.59    inference(resolution,[],[f144,f84])).
% 1.96/0.59  fof(f84,plain,(
% 1.96/0.59    ( ! [X0,X1] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f44])).
% 1.96/0.59  fof(f44,plain,(
% 1.96/0.59    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.96/0.59    inference(flattening,[],[f43])).
% 1.96/0.59  fof(f43,plain,(
% 1.96/0.59    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.96/0.59    inference(ennf_transformation,[],[f25])).
% 1.96/0.59  fof(f25,axiom,(
% 1.96/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 1.96/0.59  fof(f223,plain,(
% 1.96/0.59    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) | spl10_14),
% 1.96/0.59    inference(avatar_component_clause,[],[f221])).
% 1.96/0.59  fof(f224,plain,(
% 1.96/0.59    ~spl10_14 | spl10_12),
% 1.96/0.59    inference(avatar_split_clause,[],[f218,f209,f221])).
% 1.96/0.59  fof(f209,plain,(
% 1.96/0.59    spl10_12 <=> sP3(sK2,sK1,sK0)),
% 1.96/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.96/0.59  fof(f218,plain,(
% 1.96/0.59    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) | spl10_12),
% 1.96/0.59    inference(resolution,[],[f211,f73])).
% 1.96/0.59  fof(f73,plain,(
% 1.96/0.59    ( ! [X2,X0,X1] : (sP3(X2,X1,X0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f35])).
% 1.96/0.59  fof(f35,plain,(
% 1.96/0.59    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.96/0.59    inference(flattening,[],[f34])).
% 1.96/0.59  fof(f34,plain,(
% 1.96/0.59    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.96/0.59    inference(ennf_transformation,[],[f22])).
% 1.96/0.59  fof(f22,axiom,(
% 1.96/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).
% 1.96/0.59  fof(f211,plain,(
% 1.96/0.59    ~sP3(sK2,sK1,sK0) | spl10_12),
% 1.96/0.59    inference(avatar_component_clause,[],[f209])).
% 1.96/0.59  fof(f216,plain,(
% 1.96/0.59    ~spl10_12 | spl10_13 | ~spl10_1 | ~spl10_3 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_11),
% 1.96/0.59    inference(avatar_split_clause,[],[f207,f191,f177,f172,f147,f132,f122,f213,f209])).
% 1.96/0.59  fof(f207,plain,(
% 1.96/0.59    k1_xboole_0 = k2_struct_0(sK1) | ~sP3(sK2,sK1,sK0) | (~spl10_1 | ~spl10_3 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_11)),
% 1.96/0.59    inference(subsumption_resolution,[],[f206,f174])).
% 1.96/0.59  fof(f206,plain,(
% 1.96/0.59    k1_xboole_0 = k2_struct_0(sK1) | ~sP3(sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_3 | ~spl10_6 | ~spl10_8 | ~spl10_11)),
% 1.96/0.59    inference(subsumption_resolution,[],[f205,f193])).
% 1.96/0.59  fof(f205,plain,(
% 1.96/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | ~sP3(sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_3 | ~spl10_6 | ~spl10_8)),
% 1.96/0.59    inference(subsumption_resolution,[],[f204,f134])).
% 1.96/0.59  fof(f204,plain,(
% 1.96/0.59    ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | ~sP3(sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_6 | ~spl10_8)),
% 1.96/0.59    inference(subsumption_resolution,[],[f203,f149])).
% 1.96/0.59  fof(f203,plain,(
% 1.96/0.59    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | ~sP3(sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_8)),
% 1.96/0.59    inference(resolution,[],[f152,f179])).
% 1.96/0.59  fof(f152,plain,(
% 1.96/0.59    ( ! [X4,X3] : (~v1_funct_2(sK2,u1_struct_0(X4),u1_struct_0(X3)) | ~l1_pre_topc(X4) | ~l1_pre_topc(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3)))) | k1_xboole_0 = k2_struct_0(X3) | ~sP3(sK2,X3,X4) | v5_pre_topc(sK2,X4,X3)) ) | ~spl10_1),
% 1.96/0.59    inference(resolution,[],[f124,f77])).
% 1.96/0.59  fof(f77,plain,(
% 1.96/0.59    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k1_xboole_0 = k2_struct_0(X1) | ~sP3(X2,X1,X0) | v5_pre_topc(X2,X0,X1)) )),
% 1.96/0.59    inference(cnf_transformation,[],[f35])).
% 1.96/0.59  fof(f194,plain,(
% 1.96/0.59    spl10_11),
% 1.96/0.59    inference(avatar_split_clause,[],[f59,f191])).
% 1.96/0.59  fof(f59,plain,(
% 1.96/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.96/0.59    inference(cnf_transformation,[],[f30])).
% 1.96/0.59  fof(f30,plain,(
% 1.96/0.59    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 1.96/0.59    inference(flattening,[],[f29])).
% 1.96/0.59  fof(f29,plain,(
% 1.96/0.59    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 1.96/0.59    inference(ennf_transformation,[],[f28])).
% 1.96/0.59  fof(f28,negated_conjecture,(
% 1.96/0.59    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 1.96/0.59    inference(negated_conjecture,[],[f27])).
% 1.96/0.59  fof(f27,conjecture,(
% 1.96/0.59    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 1.96/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tex_2)).
% 1.96/0.59  fof(f180,plain,(
% 1.96/0.59    spl10_8),
% 1.96/0.59    inference(avatar_split_clause,[],[f58,f177])).
% 1.96/0.59  fof(f58,plain,(
% 1.96/0.59    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.96/0.59    inference(cnf_transformation,[],[f30])).
% 1.96/0.59  fof(f175,plain,(
% 1.96/0.59    ~spl10_7),
% 1.96/0.59    inference(avatar_split_clause,[],[f60,f172])).
% 1.96/0.59  fof(f60,plain,(
% 1.96/0.59    ~v5_pre_topc(sK2,sK0,sK1)),
% 1.96/0.59    inference(cnf_transformation,[],[f30])).
% 1.96/0.59  fof(f150,plain,(
% 1.96/0.59    spl10_6),
% 1.96/0.59    inference(avatar_split_clause,[],[f65,f147])).
% 1.96/0.59  fof(f65,plain,(
% 1.96/0.59    l1_pre_topc(sK0)),
% 1.96/0.59    inference(cnf_transformation,[],[f30])).
% 1.96/0.59  fof(f145,plain,(
% 1.96/0.59    spl10_5),
% 1.96/0.59    inference(avatar_split_clause,[],[f64,f142])).
% 1.96/0.59  fof(f64,plain,(
% 1.96/0.59    v1_tdlat_3(sK0)),
% 1.96/0.59    inference(cnf_transformation,[],[f30])).
% 1.96/0.59  fof(f140,plain,(
% 1.96/0.59    spl10_4),
% 1.96/0.59    inference(avatar_split_clause,[],[f63,f137])).
% 1.96/0.59  fof(f63,plain,(
% 1.96/0.59    v2_pre_topc(sK0)),
% 1.96/0.59    inference(cnf_transformation,[],[f30])).
% 1.96/0.59  fof(f135,plain,(
% 1.96/0.59    spl10_3),
% 1.96/0.59    inference(avatar_split_clause,[],[f62,f132])).
% 1.96/0.59  fof(f62,plain,(
% 1.96/0.59    l1_pre_topc(sK1)),
% 1.96/0.59    inference(cnf_transformation,[],[f30])).
% 1.96/0.59  fof(f130,plain,(
% 1.96/0.59    spl10_2),
% 1.96/0.59    inference(avatar_split_clause,[],[f61,f127])).
% 1.96/0.59  fof(f61,plain,(
% 1.96/0.59    v2_pre_topc(sK1)),
% 1.96/0.59    inference(cnf_transformation,[],[f30])).
% 1.96/0.59  fof(f125,plain,(
% 1.96/0.59    spl10_1),
% 1.96/0.59    inference(avatar_split_clause,[],[f57,f122])).
% 1.96/0.59  fof(f57,plain,(
% 1.96/0.59    v1_funct_1(sK2)),
% 1.96/0.59    inference(cnf_transformation,[],[f30])).
% 1.96/0.59  % SZS output end Proof for theBenchmark
% 1.96/0.59  % (21524)------------------------------
% 1.96/0.59  % (21524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.59  % (21524)Termination reason: Refutation
% 1.96/0.59  
% 1.96/0.59  % (21524)Memory used [KB]: 11513
% 1.96/0.60  % (21524)Time elapsed: 0.199 s
% 1.96/0.60  % (21524)------------------------------
% 1.96/0.60  % (21524)------------------------------
% 1.96/0.60  % (21503)Success in time 0.255 s
%------------------------------------------------------------------------------
