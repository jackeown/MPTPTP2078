%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:24 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  336 (1565 expanded)
%              Number of leaves         :   64 ( 549 expanded)
%              Depth                    :   24
%              Number of atoms          : 1297 (8195 expanded)
%              Number of equality atoms :   87 ( 606 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3341,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f490,f561,f598,f602,f948,f951,f954,f1029,f1105,f1142,f1156,f1281,f1308,f1589,f1595,f1842,f1846,f2016,f2137,f2153,f2154,f2155,f2472,f2573,f2575,f2653,f2762,f2940,f3117,f3256,f3315,f3324,f3329,f3333])).

fof(f3333,plain,
    ( ~ spl10_8
    | ~ spl10_59 ),
    inference(avatar_contradiction_clause,[],[f3331])).

fof(f3331,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_59 ),
    inference(resolution,[],[f2568,f2157])).

fof(f2157,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK1,sK2)
    | ~ spl10_8 ),
    inference(backward_demodulation,[],[f96,f583])).

fof(f583,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f582])).

fof(f582,plain,
    ( spl10_8
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f96,plain,(
    ~ v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v1_tdlat_3(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f56,f55,f54])).

fof(f54,plain,
    ( ? [X0] :
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
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,sK1,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v1_tdlat_3(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v5_pre_topc(X2,sK1,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ~ v5_pre_topc(X2,sK1,sK2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X2] :
        ( ~ v5_pre_topc(X2,sK1,sK2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
        & v1_funct_1(X2) )
   => ( ~ v5_pre_topc(sK3,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
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
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).

fof(f2568,plain,
    ( v5_pre_topc(k1_xboole_0,sK1,sK2)
    | ~ spl10_59 ),
    inference(avatar_component_clause,[],[f2566])).

fof(f2566,plain,
    ( spl10_59
  <=> v5_pre_topc(k1_xboole_0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f3329,plain,(
    spl10_106 ),
    inference(avatar_contradiction_clause,[],[f3325])).

fof(f3325,plain,
    ( $false
    | spl10_106 ),
    inference(resolution,[],[f3323,f98])).

fof(f98,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f3323,plain,
    ( ~ r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))
    | spl10_106 ),
    inference(avatar_component_clause,[],[f3321])).

fof(f3321,plain,
    ( spl10_106
  <=> r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f3324,plain,
    ( ~ spl10_4
    | ~ spl10_106
    | spl10_105 ),
    inference(avatar_split_clause,[],[f3318,f3312,f3321,f484])).

fof(f484,plain,
    ( spl10_4
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f3312,plain,
    ( spl10_105
  <=> r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_105])])).

fof(f3318,plain,
    ( ~ r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl10_105 ),
    inference(superposition,[],[f3314,f1569])).

fof(f1569,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f1567,f150])).

fof(f150,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1567,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f904,f170])).

fof(f170,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f163,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f163,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f131,f98])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f904,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f903])).

fof(f903,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f462,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f462,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f457])).

fof(f457,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f145,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f3314,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))
    | spl10_105 ),
    inference(avatar_component_clause,[],[f3312])).

fof(f3315,plain,
    ( ~ spl10_105
    | ~ spl10_4
    | spl10_66
    | ~ spl10_82 ),
    inference(avatar_split_clause,[],[f3310,f2931,f2759,f484,f3312])).

fof(f2759,plain,
    ( spl10_66
  <=> r1_tarski(k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f2931,plain,
    ( spl10_82
  <=> k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0) = k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f3310,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))
    | spl10_66
    | ~ spl10_82 ),
    inference(forward_demodulation,[],[f3308,f149])).

fof(f149,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f87])).

fof(f3308,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)))
    | spl10_66
    | ~ spl10_82 ),
    inference(superposition,[],[f3259,f140])).

fof(f3259,plain,
    ( ~ r1_tarski(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))
    | spl10_66
    | ~ spl10_82 ),
    inference(backward_demodulation,[],[f2761,f2932])).

fof(f2932,plain,
    ( k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0) = k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0))
    | ~ spl10_82 ),
    inference(avatar_component_clause,[],[f2931])).

fof(f2761,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))
    | spl10_66 ),
    inference(avatar_component_clause,[],[f2759])).

fof(f3256,plain,
    ( ~ spl10_23
    | ~ spl10_81
    | ~ spl10_83
    | spl10_82 ),
    inference(avatar_split_clause,[],[f3255,f2931,f2935,f2921,f1079])).

fof(f1079,plain,
    ( spl10_23
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f2921,plain,
    ( spl10_81
  <=> v4_pre_topc(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_81])])).

fof(f2935,plain,
    ( spl10_83
  <=> m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).

fof(f3255,plain,
    ( ~ m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v4_pre_topc(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),sK1)
    | ~ l1_pre_topc(sK1)
    | spl10_82 ),
    inference(forward_demodulation,[],[f3241,f157])).

fof(f157,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f156,f90])).

fof(f90,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f156,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f103,f104])).

fof(f104,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f103,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3241,plain,
    ( ~ v4_pre_topc(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),sK1)
    | ~ m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | spl10_82 ),
    inference(trivial_inequality_removal,[],[f3240])).

fof(f3240,plain,
    ( k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0) != k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)
    | ~ v4_pre_topc(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),sK1)
    | ~ m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | spl10_82 ),
    inference(superposition,[],[f2933,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f2933,plain,
    ( k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0) != k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0))
    | spl10_82 ),
    inference(avatar_component_clause,[],[f2931])).

fof(f3117,plain,(
    spl10_83 ),
    inference(avatar_contradiction_clause,[],[f3115])).

fof(f3115,plain,
    ( $false
    | spl10_83 ),
    inference(resolution,[],[f3113,f151])).

fof(f151,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f100,f99])).

fof(f99,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f3113,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl10_83 ),
    inference(forward_demodulation,[],[f3109,f149])).

fof(f3109,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)))
    | spl10_83 ),
    inference(resolution,[],[f2937,f462])).

fof(f2937,plain,
    ( ~ m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK1)))
    | spl10_83 ),
    inference(avatar_component_clause,[],[f2935])).

fof(f2940,plain,
    ( ~ spl10_15
    | ~ spl10_23
    | ~ spl10_42
    | ~ spl10_83
    | spl10_81 ),
    inference(avatar_split_clause,[],[f2939,f2921,f2935,f1582,f1079,f931])).

fof(f931,plain,
    ( spl10_15
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f1582,plain,
    ( spl10_42
  <=> v1_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f2939,plain,
    ( ~ m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v1_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl10_81 ),
    inference(forward_demodulation,[],[f2926,f157])).

fof(f2926,plain,
    ( ~ m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl10_81 ),
    inference(resolution,[],[f2923,f117])).

fof(f117,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK6(X0),X0)
            & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f67,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
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
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(f2923,plain,
    ( ~ v4_pre_topc(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),sK1)
    | spl10_81 ),
    inference(avatar_component_clause,[],[f2921])).

fof(f2762,plain,
    ( ~ spl10_66
    | ~ spl10_4
    | spl10_62 ),
    inference(avatar_split_clause,[],[f2757,f2650,f484,f2759])).

fof(f2650,plain,
    ( spl10_62
  <=> r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f2757,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))
    | spl10_62 ),
    inference(forward_demodulation,[],[f2754,f149])).

fof(f2754,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)))
    | spl10_62 ),
    inference(superposition,[],[f2652,f144])).

fof(f2652,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))
    | spl10_62 ),
    inference(avatar_component_clause,[],[f2650])).

fof(f2653,plain,
    ( spl10_59
    | ~ spl10_15
    | ~ spl10_23
    | ~ spl10_60
    | ~ spl10_62
    | ~ spl10_45
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f2648,f2562,f1844,f2650,f2570,f1079,f931,f2566])).

fof(f2570,plain,
    ( spl10_60
  <=> v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f1844,plain,
    ( spl10_45
  <=> ! [X1] :
        ( ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0))))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f2562,plain,
    ( spl10_58
  <=> m1_subset_1(sK7(sK1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f2648,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v5_pre_topc(k1_xboole_0,sK1,sK2)
    | ~ spl10_45
    | ~ spl10_58 ),
    inference(forward_demodulation,[],[f2646,f2576])).

fof(f2576,plain,
    ( k1_xboole_0 = sK7(sK1,sK2,k1_xboole_0)
    | ~ spl10_58 ),
    inference(resolution,[],[f2564,f170])).

fof(f2564,plain,
    ( m1_subset_1(sK7(sK1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f2562])).

fof(f2646,plain,
    ( ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v5_pre_topc(k1_xboole_0,sK1,sK2)
    | ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,sK7(sK1,sK2,k1_xboole_0))),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(sK1,sK2,k1_xboole_0))))
    | ~ spl10_45 ),
    inference(superposition,[],[f1845,f157])).

fof(f1845,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0)))) )
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f1844])).

fof(f2575,plain,
    ( ~ spl10_6
    | ~ spl10_8
    | spl10_60 ),
    inference(avatar_contradiction_clause,[],[f2574])).

fof(f2574,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_8
    | spl10_60 ),
    inference(resolution,[],[f2572,f2278])).

fof(f2278,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0)
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(backward_demodulation,[],[f2159,f1847])).

fof(f1847,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ spl10_6 ),
    inference(backward_demodulation,[],[f158,f1382])).

fof(f1382,plain,
    ( k1_xboole_0 = u1_struct_0(sK2)
    | ~ spl10_6 ),
    inference(backward_demodulation,[],[f158,f1164])).

fof(f1164,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ spl10_6 ),
    inference(backward_demodulation,[],[f158,f783])).

fof(f783,plain,
    ( k1_xboole_0 = u1_struct_0(sK2)
    | ~ spl10_6 ),
    inference(backward_demodulation,[],[f158,f576])).

fof(f576,plain,
    ( k1_xboole_0 = k2_struct_0(sK2)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f574])).

fof(f574,plain,
    ( spl10_6
  <=> k1_xboole_0 = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f158,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f156,f92])).

fof(f92,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f2159,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl10_8 ),
    inference(backward_demodulation,[],[f162,f583])).

fof(f162,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f159,f158])).

fof(f159,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f94,f157])).

fof(f94,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f2572,plain,
    ( ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0)
    | spl10_60 ),
    inference(avatar_component_clause,[],[f2570])).

fof(f2573,plain,
    ( spl10_58
    | spl10_59
    | ~ spl10_15
    | ~ spl10_23
    | ~ spl10_60
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f2559,f1840,f2570,f1079,f931,f2566,f2562])).

fof(f1840,plain,
    ( spl10_44
  <=> ! [X1] :
        ( m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f2559,plain,
    ( ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v5_pre_topc(k1_xboole_0,sK1,sK2)
    | m1_subset_1(sK7(sK1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_44 ),
    inference(superposition,[],[f1841,f157])).

fof(f1841,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f1840])).

fof(f2472,plain,
    ( ~ spl10_5
    | ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f2468])).

fof(f2468,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(resolution,[],[f2300,f98])).

fof(f2300,plain,
    ( ! [X1] : ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,k1_relat_1(k1_xboole_0)))
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(forward_demodulation,[],[f2261,f149])).

fof(f2261,plain,
    ( ! [X1] : ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0),k2_zfmisc_1(X1,k1_relat_1(k1_xboole_0)))
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(backward_demodulation,[],[f560,f1847])).

fof(f560,plain,
    ( ! [X1] : ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X1,k1_relat_1(k1_xboole_0)))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f559])).

fof(f559,plain,
    ( spl10_5
  <=> ! [X1] : ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X1,k1_relat_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f2155,plain,
    ( spl10_6
    | spl10_14 ),
    inference(avatar_split_clause,[],[f2060,f712,f574])).

fof(f712,plain,
    ( spl10_14
  <=> ! [X1] :
        ( ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))
        | ~ l1_pre_topc(X1)
        | sP0(X1,sK3,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f2060,plain,(
    ! [X1] :
      ( ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
      | sP0(X1,sK3,sK2)
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f2059,f158])).

fof(f2059,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
      | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(sK2))
      | sP0(X1,sK3,sK2)
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f2056,f158])).

fof(f2056,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
      | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(sK2))
      | sP0(X1,sK3,sK2)
      | k1_xboole_0 = k2_struct_0(sK2)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f586,f92])).

fof(f586,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
      | sP0(X1,sK3,X0)
      | k1_xboole_0 = k2_struct_0(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f110,f93])).

fof(f93,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | sP0(X0,X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f35,f52])).

fof(f52,plain,(
    ! [X0,X2,X1] :
      ( ( v5_pre_topc(X2,X0,X1)
      <=> ! [X3] :
            ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
            | ~ v3_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(f2154,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f2039,f195,f191])).

fof(f191,plain,
    ( spl10_1
  <=> sK3 = k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f195,plain,
    ( spl10_2
  <=> r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f2039,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),sK3)
    | sK3 = k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(resolution,[],[f161,f166])).

fof(f166,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | ~ r1_tarski(X4,X5)
      | X4 = X5 ) ),
    inference(resolution,[],[f131,f135])).

fof(f161,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f160,f158])).

fof(f160,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f95,f157])).

fof(f95,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f2153,plain,(
    spl10_43 ),
    inference(avatar_contradiction_clause,[],[f2151])).

fof(f2151,plain,
    ( $false
    | spl10_43 ),
    inference(resolution,[],[f1727,f161])).

fof(f1727,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))
    | spl10_43 ),
    inference(resolution,[],[f1588,f145])).

fof(f1588,plain,
    ( ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(k2_struct_0(sK1)))
    | spl10_43 ),
    inference(avatar_component_clause,[],[f1586])).

fof(f1586,plain,
    ( spl10_43
  <=> m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f2137,plain,(
    spl10_47 ),
    inference(avatar_contradiction_clause,[],[f2135])).

fof(f2135,plain,
    ( $false
    | spl10_47 ),
    inference(resolution,[],[f2014,f161])).

fof(f2014,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))
    | spl10_47 ),
    inference(avatar_component_clause,[],[f2012])).

fof(f2012,plain,
    ( spl10_47
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f2016,plain,
    ( ~ spl10_47
    | spl10_29
    | ~ spl10_23
    | ~ spl10_30
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f1109,f712,f1117,f1079,f1113,f2012])).

fof(f1113,plain,
    ( spl10_29
  <=> sP0(sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f1117,plain,
    ( spl10_30
  <=> v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f1109,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ l1_pre_topc(sK1)
    | sP0(sK1,sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))
    | ~ spl10_14 ),
    inference(superposition,[],[f713,f157])).

fof(f713,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))
        | ~ l1_pre_topc(X1)
        | sP0(X1,sK3,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) )
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f712])).

fof(f1846,plain,
    ( spl10_45
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f1402,f1027,f582,f574,f484,f1844])).

fof(f1027,plain,
    ( spl10_20
  <=> ! [X1] :
        ( ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v5_pre_topc(sK3,X1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f1402,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f1401,f149])).

fof(f1401,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f1400,f1164])).

fof(f1400,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f1394,f1164])).

fof(f1394,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_20 ),
    inference(backward_demodulation,[],[f1371,f1164])).

fof(f1371,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k2_struct_0(sK2))
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_8
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f1370,f583])).

fof(f1370,plain,
    ( ! [X1] :
        ( v5_pre_topc(k1_xboole_0,X1,sK2)
        | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) )
    | ~ spl10_8
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f1369,f583])).

fof(f1369,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v5_pre_topc(sK3,X1,sK2)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) )
    | ~ spl10_8
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f1333,f583])).

fof(f1333,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v5_pre_topc(sK3,X1,sK2)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) )
    | ~ spl10_8
    | ~ spl10_20 ),
    inference(backward_demodulation,[],[f1028,f583])).

fof(f1028,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v5_pre_topc(sK3,X1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) )
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f1027])).

fof(f1842,plain,
    ( spl10_44
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f1399,f946,f582,f574,f484,f1840])).

fof(f946,plain,
    ( spl10_18
  <=> ! [X1] :
        ( m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v5_pre_topc(sK3,X1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f1399,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f1398,f149])).

fof(f1398,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f1397,f1164])).

fof(f1397,plain,
    ( ! [X1] :
        ( m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f1393,f1164])).

fof(f1393,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f1363,f1164])).

fof(f1363,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),k2_struct_0(sK2))
        | v5_pre_topc(k1_xboole_0,X1,sK2)
        | m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f1362,f583])).

fof(f1362,plain,
    ( ! [X1] :
        ( v5_pre_topc(k1_xboole_0,X1,sK2)
        | m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) )
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f1361,f583])).

fof(f1361,plain,
    ( ! [X1] :
        ( m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v5_pre_topc(sK3,X1,sK2)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) )
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f1330,f583])).

fof(f1330,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v5_pre_topc(sK3,X1,sK2)
        | ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) )
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f947,f583])).

fof(f947,plain,
    ( ! [X1] :
        ( m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v5_pre_topc(sK3,X1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
        | ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) )
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f946])).

fof(f1595,plain,(
    spl10_42 ),
    inference(avatar_contradiction_clause,[],[f1590])).

fof(f1590,plain,
    ( $false
    | spl10_42 ),
    inference(resolution,[],[f1584,f89])).

fof(f89,plain,(
    v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f1584,plain,
    ( ~ v1_tdlat_3(sK1)
    | spl10_42 ),
    inference(avatar_component_clause,[],[f1582])).

fof(f1589,plain,
    ( ~ spl10_15
    | ~ spl10_23
    | ~ spl10_42
    | ~ spl10_43
    | spl10_36 ),
    inference(avatar_split_clause,[],[f1580,f1153,f1586,f1582,f1079,f931])).

fof(f1153,plain,
    ( spl10_36
  <=> v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f1580,plain,
    ( ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v1_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl10_36 ),
    inference(forward_demodulation,[],[f1579,f157])).

fof(f1579,plain,
    ( ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl10_36 ),
    inference(resolution,[],[f1155,f114])).

fof(f114,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK5(X0),X0)
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f1155,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1)
    | spl10_36 ),
    inference(avatar_component_clause,[],[f1153])).

fof(f1308,plain,(
    ~ spl10_35 ),
    inference(avatar_contradiction_clause,[],[f1306])).

fof(f1306,plain,
    ( $false
    | ~ spl10_35 ),
    inference(resolution,[],[f1151,f96])).

fof(f1151,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f1149,plain,
    ( spl10_35
  <=> v5_pre_topc(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f1281,plain,
    ( ~ spl10_1
    | ~ spl10_6
    | spl10_10 ),
    inference(avatar_contradiction_clause,[],[f1278])).

fof(f1278,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_6
    | spl10_10 ),
    inference(resolution,[],[f1181,f97])).

fof(f97,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1181,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_1
    | ~ spl10_6
    | spl10_10 ),
    inference(backward_demodulation,[],[f629,f1175])).

fof(f1175,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_1
    | ~ spl10_6 ),
    inference(forward_demodulation,[],[f1166,f149])).

fof(f1166,plain,
    ( sK3 = k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)
    | ~ spl10_1
    | ~ spl10_6 ),
    inference(backward_demodulation,[],[f193,f1164])).

fof(f193,plain,
    ( sK3 = k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f191])).

fof(f629,plain,
    ( ~ v1_xboole_0(sK3)
    | spl10_10 ),
    inference(resolution,[],[f603,f123])).

fof(f123,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f75,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f603,plain,
    ( r2_hidden(sK9(sK3,k1_xboole_0),sK3)
    | spl10_10 ),
    inference(resolution,[],[f596,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f82,f83])).

% (7934)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
fof(f83,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f596,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl10_10 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl10_10
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f1156,plain,
    ( spl10_35
    | ~ spl10_36
    | ~ spl10_29 ),
    inference(avatar_split_clause,[],[f1147,f1113,f1153,f1149])).

fof(f1147,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1)
    | v5_pre_topc(sK3,sK1,sK2)
    | ~ spl10_29 ),
    inference(forward_demodulation,[],[f1146,f157])).

fof(f1146,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1)
    | v5_pre_topc(sK3,sK1,sK2)
    | ~ spl10_29 ),
    inference(forward_demodulation,[],[f1144,f158])).

fof(f1144,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1)
    | v5_pre_topc(sK3,sK1,sK2)
    | ~ spl10_29 ),
    inference(resolution,[],[f1115,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK4(X0,X1,X2)),X0)
      | v5_pre_topc(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X1,X0,X2)
          | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK4(X0,X1,X2)),X0)
            & v3_pre_topc(sK4(X0,X1,X2),X2)
            & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) )
        & ( ! [X4] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
              | ~ v3_pre_topc(X4,X2)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
          | ~ v5_pre_topc(X1,X0,X2) ) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
          & v3_pre_topc(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK4(X0,X1,X2)),X0)
        & v3_pre_topc(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X1,X0,X2)
          | ? [X3] :
              ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
              & v3_pre_topc(X3,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
        & ( ! [X4] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
              | ~ v3_pre_topc(X4,X2)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
          | ~ v5_pre_topc(X1,X0,X2) ) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X2,X1] :
      ( ( ( v5_pre_topc(X2,X0,X1)
          | ? [X3] :
              ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
              & v3_pre_topc(X3,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ! [X3] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ v5_pre_topc(X2,X0,X1) ) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f1115,plain,
    ( sP0(sK1,sK3,sK2)
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f1113])).

fof(f1142,plain,(
    spl10_30 ),
    inference(avatar_contradiction_clause,[],[f1141])).

fof(f1141,plain,
    ( $false
    | spl10_30 ),
    inference(resolution,[],[f1119,f162])).

fof(f1119,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2))
    | spl10_30 ),
    inference(avatar_component_clause,[],[f1117])).

fof(f1105,plain,(
    spl10_23 ),
    inference(avatar_contradiction_clause,[],[f1104])).

fof(f1104,plain,
    ( $false
    | spl10_23 ),
    inference(resolution,[],[f1081,f90])).

fof(f1081,plain,
    ( ~ l1_pre_topc(sK1)
    | spl10_23 ),
    inference(avatar_component_clause,[],[f1079])).

fof(f1029,plain,
    ( ~ spl10_17
    | spl10_20 ),
    inference(avatar_split_clause,[],[f1025,f1027,f942])).

fof(f942,plain,
    ( spl10_17
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f1025,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3))))
      | ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
      | v5_pre_topc(sK3,X1,sK2)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f1024,f158])).

fof(f1024,plain,(
    ! [X1] :
      ( ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
      | v5_pre_topc(sK3,X1,sK2)
      | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3))))
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f1023,f158])).

fof(f1023,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
      | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(sK2))
      | v5_pre_topc(sK3,X1,sK2)
      | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3))))
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f1015,f158])).

fof(f1015,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
      | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(sK2))
      | v5_pre_topc(sK3,X1,sK2)
      | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3))))
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f679,f92])).

fof(f679,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(sK3,X0,X1)
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,sK7(X0,X1,sK3))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k2_pre_topc(X1,sK7(X0,X1,sK3))))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f122,f93])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2))))
                    & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f71,f72])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2))))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).

fof(f954,plain,(
    spl10_17 ),
    inference(avatar_contradiction_clause,[],[f952])).

fof(f952,plain,
    ( $false
    | spl10_17 ),
    inference(resolution,[],[f944,f91])).

fof(f91,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f944,plain,
    ( ~ v2_pre_topc(sK2)
    | spl10_17 ),
    inference(avatar_component_clause,[],[f942])).

fof(f951,plain,(
    spl10_15 ),
    inference(avatar_contradiction_clause,[],[f949])).

fof(f949,plain,
    ( $false
    | spl10_15 ),
    inference(resolution,[],[f933,f88])).

fof(f88,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f933,plain,
    ( ~ v2_pre_topc(sK1)
    | spl10_15 ),
    inference(avatar_component_clause,[],[f931])).

fof(f948,plain,
    ( ~ spl10_17
    | spl10_18 ),
    inference(avatar_split_clause,[],[f940,f946,f942])).

fof(f940,plain,(
    ! [X1] :
      ( m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
      | v5_pre_topc(sK3,X1,sK2)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f939,f158])).

fof(f939,plain,(
    ! [X1] :
      ( ~ v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
      | v5_pre_topc(sK3,X1,sK2)
      | m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f938,f158])).

fof(f938,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))
      | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(sK2))
      | v5_pre_topc(sK3,X1,sK2)
      | m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f926,f158])).

fof(f926,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
      | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(sK2))
      | v5_pre_topc(sK3,X1,sK2)
      | m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f639,f92])).

fof(f639,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(sK3,X0,X1)
      | m1_subset_1(sK7(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f121,f93])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f602,plain,(
    spl10_9 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | spl10_9 ),
    inference(resolution,[],[f592,f98])).

fof(f592,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl10_9 ),
    inference(avatar_component_clause,[],[f590])).

fof(f590,plain,
    ( spl10_9
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f598,plain,
    ( ~ spl10_10
    | ~ spl10_9
    | spl10_8 ),
    inference(avatar_split_clause,[],[f588,f582,f590,f594])).

fof(f588,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ r1_tarski(sK3,k1_xboole_0)
    | spl10_8 ),
    inference(extensionality_resolution,[],[f131,f584])).

fof(f584,plain,
    ( k1_xboole_0 != sK3
    | spl10_8 ),
    inference(avatar_component_clause,[],[f582])).

fof(f561,plain,
    ( spl10_5
    | ~ spl10_4
    | spl10_2 ),
    inference(avatar_split_clause,[],[f557,f195,f484,f559])).

fof(f557,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X1,k1_relat_1(k1_xboole_0))) )
    | spl10_2 ),
    inference(forward_demodulation,[],[f555,f150])).

fof(f555,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X1,k1_relat_1(k1_xboole_0)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | spl10_2 ),
    inference(superposition,[],[f549,f140])).

fof(f549,plain,
    ( ! [X0,X1] : ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X0,k1_relset_1(k1_xboole_0,X1,k1_xboole_0)))
    | spl10_2 ),
    inference(resolution,[],[f466,f151])).

fof(f466,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k1_xboole_0))
        | ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X8,k1_relset_1(k1_xboole_0,X6,X7))) )
    | spl10_2 ),
    inference(duplicate_literal_removal,[],[f465])).

fof(f465,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k1_xboole_0))
        | ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X8,k1_relset_1(k1_xboole_0,X6,X7)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_xboole_0)) )
    | spl10_2 ),
    inference(forward_demodulation,[],[f459,f150])).

fof(f459,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X8,k1_relset_1(k1_xboole_0,X6,X7)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6))) )
    | spl10_2 ),
    inference(superposition,[],[f375,f144])).

fof(f375,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X6,k8_relset_1(k1_xboole_0,X5,X4,X7)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) )
    | spl10_2 ),
    inference(forward_demodulation,[],[f371,f150])).

fof(f371,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
        | ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X6,k8_relset_1(k1_xboole_0,X5,X4,X7))) )
    | spl10_2 ),
    inference(resolution,[],[f145,f291])).

fof(f291,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k1_xboole_0))
        | ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X4,X5)) )
    | spl10_2 ),
    inference(resolution,[],[f250,f135])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X1,X0)) )
    | spl10_2 ),
    inference(resolution,[],[f246,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(X0,k1_xboole_0) )
    | spl10_2 ),
    inference(resolution,[],[f245,f97])).

fof(f245,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_xboole_0(X6)
        | ~ r1_tarski(X5,X6)
        | ~ m1_subset_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | spl10_2 ),
    inference(resolution,[],[f223,f123])).

fof(f223,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK8(X1),X2)
        | ~ m1_subset_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(X1,X2) )
    | spl10_2 ),
    inference(resolution,[],[f210,f132])).

fof(f132,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f210,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK8(X6),X6)
        | ~ m1_subset_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) )
    | spl10_2 ),
    inference(resolution,[],[f206,f124])).

fof(f124,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK8(X0),X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | spl10_2 ),
    inference(resolution,[],[f205,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f205,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))
    | spl10_2 ),
    inference(resolution,[],[f201,f123])).

fof(f201,plain,
    ( r2_hidden(sK9(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),sK3),k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))
    | spl10_2 ),
    inference(resolution,[],[f197,f133])).

fof(f197,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),sK3)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f195])).

fof(f490,plain,(
    spl10_4 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | spl10_4 ),
    inference(resolution,[],[f486,f151])).

fof(f486,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl10_4 ),
    inference(avatar_component_clause,[],[f484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:04:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (7869)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (7885)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (7870)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (7865)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (7878)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (7868)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (7866)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (7871)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (7876)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (7876)Refutation not found, incomplete strategy% (7876)------------------------------
% 0.21/0.52  % (7876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7876)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7876)Memory used [KB]: 10618
% 0.21/0.52  % (7876)Time elapsed: 0.116 s
% 0.21/0.52  % (7876)------------------------------
% 0.21/0.52  % (7876)------------------------------
% 0.21/0.52  % (7888)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (7880)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (7872)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (7881)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (7886)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (7865)Refutation not found, incomplete strategy% (7865)------------------------------
% 0.21/0.53  % (7865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7865)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7865)Memory used [KB]: 1663
% 0.21/0.53  % (7865)Time elapsed: 0.003 s
% 0.21/0.53  % (7865)------------------------------
% 0.21/0.53  % (7865)------------------------------
% 0.21/0.53  % (7877)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (7877)Refutation not found, incomplete strategy% (7877)------------------------------
% 0.21/0.53  % (7877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7877)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7877)Memory used [KB]: 10618
% 0.21/0.53  % (7877)Time elapsed: 0.133 s
% 0.21/0.53  % (7877)------------------------------
% 0.21/0.53  % (7877)------------------------------
% 0.21/0.53  % (7875)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (7883)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (7879)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (7883)Refutation not found, incomplete strategy% (7883)------------------------------
% 0.21/0.53  % (7883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7883)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7883)Memory used [KB]: 10618
% 0.21/0.53  % (7883)Time elapsed: 0.133 s
% 0.21/0.53  % (7883)------------------------------
% 0.21/0.53  % (7883)------------------------------
% 0.21/0.53  % (7873)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (7867)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (7889)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (7893)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (7892)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (7890)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (7891)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (7895)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (7888)Refutation not found, incomplete strategy% (7888)------------------------------
% 0.21/0.54  % (7888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7888)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7888)Memory used [KB]: 11001
% 0.21/0.54  % (7888)Time elapsed: 0.083 s
% 0.21/0.54  % (7888)------------------------------
% 0.21/0.54  % (7888)------------------------------
% 0.21/0.54  % (7894)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (7884)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (7882)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (7887)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.55  % (7875)Refutation not found, incomplete strategy% (7875)------------------------------
% 1.47/0.55  % (7875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (7875)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (7875)Memory used [KB]: 10618
% 1.47/0.55  % (7875)Time elapsed: 0.002 s
% 1.47/0.55  % (7875)------------------------------
% 1.47/0.55  % (7875)------------------------------
% 1.60/0.58  % (7887)Refutation not found, incomplete strategy% (7887)------------------------------
% 1.60/0.58  % (7887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (7887)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (7887)Memory used [KB]: 1918
% 1.60/0.58  % (7887)Time elapsed: 0.181 s
% 1.60/0.58  % (7887)------------------------------
% 1.60/0.58  % (7887)------------------------------
% 1.60/0.61  % (7886)Refutation not found, incomplete strategy% (7886)------------------------------
% 1.60/0.61  % (7886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.62  % (7886)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.62  
% 1.60/0.62  % (7886)Memory used [KB]: 11641
% 1.60/0.62  % (7886)Time elapsed: 0.220 s
% 1.60/0.62  % (7886)------------------------------
% 1.60/0.62  % (7886)------------------------------
% 2.21/0.66  % (7923)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.21/0.67  % (7922)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.21/0.67  % (7924)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.21/0.68  % (7926)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.21/0.69  % (7925)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.21/0.70  % (7927)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.21/0.71  % (7928)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.21/0.73  % (7878)Refutation found. Thanks to Tanya!
% 2.21/0.73  % SZS status Theorem for theBenchmark
% 2.66/0.74  % SZS output start Proof for theBenchmark
% 2.66/0.74  fof(f3341,plain,(
% 2.66/0.74    $false),
% 2.66/0.74    inference(avatar_sat_refutation,[],[f490,f561,f598,f602,f948,f951,f954,f1029,f1105,f1142,f1156,f1281,f1308,f1589,f1595,f1842,f1846,f2016,f2137,f2153,f2154,f2155,f2472,f2573,f2575,f2653,f2762,f2940,f3117,f3256,f3315,f3324,f3329,f3333])).
% 2.66/0.74  fof(f3333,plain,(
% 2.66/0.74    ~spl10_8 | ~spl10_59),
% 2.66/0.74    inference(avatar_contradiction_clause,[],[f3331])).
% 2.66/0.74  fof(f3331,plain,(
% 2.66/0.74    $false | (~spl10_8 | ~spl10_59)),
% 2.66/0.74    inference(resolution,[],[f2568,f2157])).
% 2.66/0.74  fof(f2157,plain,(
% 2.66/0.74    ~v5_pre_topc(k1_xboole_0,sK1,sK2) | ~spl10_8),
% 2.66/0.74    inference(backward_demodulation,[],[f96,f583])).
% 2.66/0.74  fof(f583,plain,(
% 2.66/0.74    k1_xboole_0 = sK3 | ~spl10_8),
% 2.66/0.74    inference(avatar_component_clause,[],[f582])).
% 2.66/0.74  fof(f582,plain,(
% 2.66/0.74    spl10_8 <=> k1_xboole_0 = sK3),
% 2.66/0.74    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 2.66/0.74  fof(f96,plain,(
% 2.66/0.74    ~v5_pre_topc(sK3,sK1,sK2)),
% 2.66/0.74    inference(cnf_transformation,[],[f57])).
% 2.66/0.74  fof(f57,plain,(
% 2.66/0.74    ((~v5_pre_topc(sK3,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v1_tdlat_3(sK1) & v2_pre_topc(sK1)),
% 2.66/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f56,f55,f54])).
% 2.66/0.74  fof(f54,plain,(
% 2.66/0.74    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v5_pre_topc(X2,sK1,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK1) & v1_tdlat_3(sK1) & v2_pre_topc(sK1))),
% 2.66/0.74    introduced(choice_axiom,[])).
% 2.66/0.74  fof(f55,plain,(
% 2.66/0.74    ? [X1] : (? [X2] : (~v5_pre_topc(X2,sK1,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (~v5_pre_topc(X2,sK1,sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 2.66/0.74    introduced(choice_axiom,[])).
% 2.66/0.74  fof(f56,plain,(
% 2.66/0.74    ? [X2] : (~v5_pre_topc(X2,sK1,sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) => (~v5_pre_topc(sK3,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3))),
% 2.66/0.74    introduced(choice_axiom,[])).
% 2.66/0.74  fof(f29,plain,(
% 2.66/0.74    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 2.66/0.74    inference(flattening,[],[f28])).
% 2.66/0.74  fof(f28,plain,(
% 2.66/0.74    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 2.66/0.74    inference(ennf_transformation,[],[f27])).
% 2.66/0.74  fof(f27,negated_conjecture,(
% 2.66/0.74    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 2.66/0.74    inference(negated_conjecture,[],[f26])).
% 2.66/0.75  fof(f26,conjecture,(
% 2.66/0.75    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).
% 2.66/0.75  fof(f2568,plain,(
% 2.66/0.75    v5_pre_topc(k1_xboole_0,sK1,sK2) | ~spl10_59),
% 2.66/0.75    inference(avatar_component_clause,[],[f2566])).
% 2.66/0.75  fof(f2566,plain,(
% 2.66/0.75    spl10_59 <=> v5_pre_topc(k1_xboole_0,sK1,sK2)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).
% 2.66/0.75  fof(f3329,plain,(
% 2.66/0.75    spl10_106),
% 2.66/0.75    inference(avatar_contradiction_clause,[],[f3325])).
% 2.66/0.75  fof(f3325,plain,(
% 2.66/0.75    $false | spl10_106),
% 2.66/0.75    inference(resolution,[],[f3323,f98])).
% 2.66/0.75  fof(f98,plain,(
% 2.66/0.75    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f5])).
% 2.66/0.75  fof(f5,axiom,(
% 2.66/0.75    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.66/0.75  fof(f3323,plain,(
% 2.66/0.75    ~r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) | spl10_106),
% 2.66/0.75    inference(avatar_component_clause,[],[f3321])).
% 2.66/0.75  fof(f3321,plain,(
% 2.66/0.75    spl10_106 <=> r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).
% 2.66/0.75  fof(f3324,plain,(
% 2.66/0.75    ~spl10_4 | ~spl10_106 | spl10_105),
% 2.66/0.75    inference(avatar_split_clause,[],[f3318,f3312,f3321,f484])).
% 2.66/0.75  fof(f484,plain,(
% 2.66/0.75    spl10_4 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 2.66/0.75  fof(f3312,plain,(
% 2.66/0.75    spl10_105 <=> r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_105])])).
% 2.66/0.75  fof(f3318,plain,(
% 2.66/0.75    ~r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl10_105),
% 2.66/0.75    inference(superposition,[],[f3314,f1569])).
% 2.66/0.75  fof(f1569,plain,(
% 2.66/0.75    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 2.66/0.75    inference(forward_demodulation,[],[f1567,f150])).
% 2.66/0.75  fof(f150,plain,(
% 2.66/0.75    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.66/0.75    inference(equality_resolution,[],[f138])).
% 2.66/0.75  fof(f138,plain,(
% 2.66/0.75    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.66/0.75    inference(cnf_transformation,[],[f87])).
% 2.66/0.75  fof(f87,plain,(
% 2.66/0.75    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.66/0.75    inference(flattening,[],[f86])).
% 2.66/0.75  fof(f86,plain,(
% 2.66/0.75    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.66/0.75    inference(nnf_transformation,[],[f6])).
% 2.66/0.75  fof(f6,axiom,(
% 2.66/0.75    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.66/0.75  fof(f1567,plain,(
% 2.66/0.75    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relat_1(X0)) )),
% 2.66/0.75    inference(resolution,[],[f904,f170])).
% 2.66/0.75  fof(f170,plain,(
% 2.66/0.75    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X1) )),
% 2.66/0.75    inference(resolution,[],[f163,f135])).
% 2.66/0.75  fof(f135,plain,(
% 2.66/0.75    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.66/0.75    inference(cnf_transformation,[],[f85])).
% 2.66/0.75  fof(f85,plain,(
% 2.66/0.75    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.66/0.75    inference(nnf_transformation,[],[f9])).
% 2.66/0.75  fof(f9,axiom,(
% 2.66/0.75    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.66/0.75  fof(f163,plain,(
% 2.66/0.75    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.66/0.75    inference(resolution,[],[f131,f98])).
% 2.66/0.75  fof(f131,plain,(
% 2.66/0.75    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f80])).
% 2.66/0.75  fof(f80,plain,(
% 2.66/0.75    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.66/0.75    inference(flattening,[],[f79])).
% 2.66/0.75  fof(f79,plain,(
% 2.66/0.75    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.66/0.75    inference(nnf_transformation,[],[f4])).
% 2.66/0.75  fof(f4,axiom,(
% 2.66/0.75    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.66/0.75  fof(f904,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.75    inference(duplicate_literal_removal,[],[f903])).
% 2.66/0.75  fof(f903,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.75    inference(superposition,[],[f462,f140])).
% 2.66/0.75  fof(f140,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.75    inference(cnf_transformation,[],[f48])).
% 2.66/0.75  fof(f48,plain,(
% 2.66/0.75    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.75    inference(ennf_transformation,[],[f14])).
% 2.66/0.75  fof(f14,axiom,(
% 2.66/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.66/0.75  fof(f462,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.75    inference(duplicate_literal_removal,[],[f457])).
% 2.66/0.75  fof(f457,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.75    inference(superposition,[],[f145,f144])).
% 2.66/0.75  fof(f144,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.75    inference(cnf_transformation,[],[f50])).
% 2.66/0.75  fof(f50,plain,(
% 2.66/0.75    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.75    inference(ennf_transformation,[],[f15])).
% 2.66/0.75  fof(f15,axiom,(
% 2.66/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 2.66/0.75  fof(f145,plain,(
% 2.66/0.75    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.75    inference(cnf_transformation,[],[f51])).
% 2.66/0.75  fof(f51,plain,(
% 2.66/0.75    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.75    inference(ennf_transformation,[],[f13])).
% 2.66/0.75  fof(f13,axiom,(
% 2.66/0.75    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 2.66/0.75  fof(f3314,plain,(
% 2.66/0.75    ~r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) | spl10_105),
% 2.66/0.75    inference(avatar_component_clause,[],[f3312])).
% 2.66/0.75  fof(f3315,plain,(
% 2.66/0.75    ~spl10_105 | ~spl10_4 | spl10_66 | ~spl10_82),
% 2.66/0.75    inference(avatar_split_clause,[],[f3310,f2931,f2759,f484,f3312])).
% 2.66/0.75  fof(f2759,plain,(
% 2.66/0.75    spl10_66 <=> r1_tarski(k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).
% 2.66/0.75  fof(f2931,plain,(
% 2.66/0.75    spl10_82 <=> k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0) = k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).
% 2.66/0.75  fof(f3310,plain,(
% 2.66/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) | (spl10_66 | ~spl10_82)),
% 2.66/0.75    inference(forward_demodulation,[],[f3308,f149])).
% 2.66/0.75  fof(f149,plain,(
% 2.66/0.75    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.66/0.75    inference(equality_resolution,[],[f139])).
% 2.66/0.75  fof(f139,plain,(
% 2.66/0.75    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.66/0.75    inference(cnf_transformation,[],[f87])).
% 2.66/0.75  fof(f3308,plain,(
% 2.66/0.75    ~r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) | (spl10_66 | ~spl10_82)),
% 2.66/0.75    inference(superposition,[],[f3259,f140])).
% 2.66/0.75  fof(f3259,plain,(
% 2.66/0.75    ~r1_tarski(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) | (spl10_66 | ~spl10_82)),
% 2.66/0.75    inference(backward_demodulation,[],[f2761,f2932])).
% 2.66/0.75  fof(f2932,plain,(
% 2.66/0.75    k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0) = k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)) | ~spl10_82),
% 2.66/0.75    inference(avatar_component_clause,[],[f2931])).
% 2.66/0.75  fof(f2761,plain,(
% 2.66/0.75    ~r1_tarski(k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) | spl10_66),
% 2.66/0.75    inference(avatar_component_clause,[],[f2759])).
% 2.66/0.75  fof(f3256,plain,(
% 2.66/0.75    ~spl10_23 | ~spl10_81 | ~spl10_83 | spl10_82),
% 2.66/0.75    inference(avatar_split_clause,[],[f3255,f2931,f2935,f2921,f1079])).
% 2.66/0.75  fof(f1079,plain,(
% 2.66/0.75    spl10_23 <=> l1_pre_topc(sK1)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 2.66/0.75  fof(f2921,plain,(
% 2.66/0.75    spl10_81 <=> v4_pre_topc(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),sK1)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_81])])).
% 2.66/0.75  fof(f2935,plain,(
% 2.66/0.75    spl10_83 <=> m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK1)))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).
% 2.66/0.75  fof(f3255,plain,(
% 2.66/0.75    ~m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK1))) | ~v4_pre_topc(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),sK1) | ~l1_pre_topc(sK1) | spl10_82),
% 2.66/0.75    inference(forward_demodulation,[],[f3241,f157])).
% 2.66/0.75  fof(f157,plain,(
% 2.66/0.75    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 2.66/0.75    inference(resolution,[],[f156,f90])).
% 2.66/0.75  fof(f90,plain,(
% 2.66/0.75    l1_pre_topc(sK1)),
% 2.66/0.75    inference(cnf_transformation,[],[f57])).
% 2.66/0.75  fof(f156,plain,(
% 2.66/0.75    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.66/0.75    inference(resolution,[],[f103,f104])).
% 2.66/0.75  fof(f104,plain,(
% 2.66/0.75    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f31])).
% 2.66/0.75  fof(f31,plain,(
% 2.66/0.75    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.66/0.75    inference(ennf_transformation,[],[f19])).
% 2.66/0.75  fof(f19,axiom,(
% 2.66/0.75    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.66/0.75  fof(f103,plain,(
% 2.66/0.75    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f30])).
% 2.66/0.75  fof(f30,plain,(
% 2.66/0.75    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.66/0.75    inference(ennf_transformation,[],[f18])).
% 2.66/0.75  fof(f18,axiom,(
% 2.66/0.75    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.66/0.75  fof(f3241,plain,(
% 2.66/0.75    ~v4_pre_topc(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),sK1) | ~m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | spl10_82),
% 2.66/0.75    inference(trivial_inequality_removal,[],[f3240])).
% 2.66/0.75  fof(f3240,plain,(
% 2.66/0.75    k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0) != k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0) | ~v4_pre_topc(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),sK1) | ~m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | spl10_82),
% 2.66/0.75    inference(superposition,[],[f2933,f112])).
% 2.66/0.75  fof(f112,plain,(
% 2.66/0.75    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f37])).
% 2.66/0.75  fof(f37,plain,(
% 2.66/0.75    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.75    inference(flattening,[],[f36])).
% 2.66/0.75  fof(f36,plain,(
% 2.66/0.75    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.75    inference(ennf_transformation,[],[f20])).
% 2.66/0.75  fof(f20,axiom,(
% 2.66/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.66/0.75  fof(f2933,plain,(
% 2.66/0.75    k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0) != k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)) | spl10_82),
% 2.66/0.75    inference(avatar_component_clause,[],[f2931])).
% 2.66/0.75  fof(f3117,plain,(
% 2.66/0.75    spl10_83),
% 2.66/0.75    inference(avatar_contradiction_clause,[],[f3115])).
% 2.66/0.75  fof(f3115,plain,(
% 2.66/0.75    $false | spl10_83),
% 2.66/0.75    inference(resolution,[],[f3113,f151])).
% 2.66/0.75  fof(f151,plain,(
% 2.66/0.75    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.66/0.75    inference(forward_demodulation,[],[f100,f99])).
% 2.66/0.75  fof(f99,plain,(
% 2.66/0.75    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.66/0.75    inference(cnf_transformation,[],[f7])).
% 2.66/0.75  fof(f7,axiom,(
% 2.66/0.75    ! [X0] : k2_subset_1(X0) = X0),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.66/0.75  fof(f100,plain,(
% 2.66/0.75    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.66/0.75    inference(cnf_transformation,[],[f8])).
% 2.66/0.75  fof(f8,axiom,(
% 2.66/0.75    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.66/0.75  fof(f3113,plain,(
% 2.66/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl10_83),
% 2.66/0.75    inference(forward_demodulation,[],[f3109,f149])).
% 2.66/0.75  fof(f3109,plain,(
% 2.66/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) | spl10_83),
% 2.66/0.75    inference(resolution,[],[f2937,f462])).
% 2.66/0.75  fof(f2937,plain,(
% 2.66/0.75    ~m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK1))) | spl10_83),
% 2.66/0.75    inference(avatar_component_clause,[],[f2935])).
% 2.66/0.75  fof(f2940,plain,(
% 2.66/0.75    ~spl10_15 | ~spl10_23 | ~spl10_42 | ~spl10_83 | spl10_81),
% 2.66/0.75    inference(avatar_split_clause,[],[f2939,f2921,f2935,f1582,f1079,f931])).
% 2.66/0.75  fof(f931,plain,(
% 2.66/0.75    spl10_15 <=> v2_pre_topc(sK1)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 2.66/0.75  fof(f1582,plain,(
% 2.66/0.75    spl10_42 <=> v1_tdlat_3(sK1)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).
% 2.66/0.75  fof(f2939,plain,(
% 2.66/0.75    ~m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK1))) | ~v1_tdlat_3(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl10_81),
% 2.66/0.75    inference(forward_demodulation,[],[f2926,f157])).
% 2.66/0.75  fof(f2926,plain,(
% 2.66/0.75    ~m1_subset_1(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_tdlat_3(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl10_81),
% 2.66/0.75    inference(resolution,[],[f2923,f117])).
% 2.66/0.75  fof(f117,plain,(
% 2.66/0.75    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f69])).
% 2.66/0.75  fof(f69,plain,(
% 2.66/0.75    ! [X0] : (((v1_tdlat_3(X0) | (~v4_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f67,f68])).
% 2.66/0.75  fof(f68,plain,(
% 2.66/0.75    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.66/0.75    introduced(choice_axiom,[])).
% 2.66/0.75  fof(f67,plain,(
% 2.66/0.75    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.75    inference(rectify,[],[f66])).
% 2.66/0.75  fof(f66,plain,(
% 2.66/0.75    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.75    inference(nnf_transformation,[],[f41])).
% 2.66/0.75  fof(f41,plain,(
% 2.66/0.75    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.75    inference(flattening,[],[f40])).
% 2.66/0.75  fof(f40,plain,(
% 2.66/0.75    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.66/0.75    inference(ennf_transformation,[],[f25])).
% 2.66/0.75  fof(f25,axiom,(
% 2.66/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).
% 2.66/0.75  fof(f2923,plain,(
% 2.66/0.75    ~v4_pre_topc(k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0),sK1) | spl10_81),
% 2.66/0.75    inference(avatar_component_clause,[],[f2921])).
% 2.66/0.75  fof(f2762,plain,(
% 2.66/0.75    ~spl10_66 | ~spl10_4 | spl10_62),
% 2.66/0.75    inference(avatar_split_clause,[],[f2757,f2650,f484,f2759])).
% 2.66/0.75  fof(f2650,plain,(
% 2.66/0.75    spl10_62 <=> r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0)))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).
% 2.66/0.75  fof(f2757,plain,(
% 2.66/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) | spl10_62),
% 2.66/0.75    inference(forward_demodulation,[],[f2754,f149])).
% 2.66/0.75  fof(f2754,plain,(
% 2.66/0.75    ~r1_tarski(k2_pre_topc(sK1,k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) | spl10_62),
% 2.66/0.75    inference(superposition,[],[f2652,f144])).
% 2.66/0.75  fof(f2652,plain,(
% 2.66/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) | spl10_62),
% 2.66/0.75    inference(avatar_component_clause,[],[f2650])).
% 2.66/0.75  fof(f2653,plain,(
% 2.66/0.75    spl10_59 | ~spl10_15 | ~spl10_23 | ~spl10_60 | ~spl10_62 | ~spl10_45 | ~spl10_58),
% 2.66/0.75    inference(avatar_split_clause,[],[f2648,f2562,f1844,f2650,f2570,f1079,f931,f2566])).
% 2.66/0.75  fof(f2570,plain,(
% 2.66/0.75    spl10_60 <=> v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).
% 2.66/0.75  fof(f1844,plain,(
% 2.66/0.75    spl10_45 <=> ! [X1] : (~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0)))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v5_pre_topc(k1_xboole_0,X1,sK2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).
% 2.66/0.75  fof(f2562,plain,(
% 2.66/0.75    spl10_58 <=> m1_subset_1(sK7(sK1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).
% 2.66/0.75  fof(f2648,plain,(
% 2.66/0.75    ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v5_pre_topc(k1_xboole_0,sK1,sK2) | (~spl10_45 | ~spl10_58)),
% 2.66/0.75    inference(forward_demodulation,[],[f2646,f2576])).
% 2.66/0.75  fof(f2576,plain,(
% 2.66/0.75    k1_xboole_0 = sK7(sK1,sK2,k1_xboole_0) | ~spl10_58),
% 2.66/0.75    inference(resolution,[],[f2564,f170])).
% 2.66/0.75  fof(f2564,plain,(
% 2.66/0.75    m1_subset_1(sK7(sK1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl10_58),
% 2.66/0.75    inference(avatar_component_clause,[],[f2562])).
% 2.66/0.75  fof(f2646,plain,(
% 2.66/0.75    ~v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v5_pre_topc(k1_xboole_0,sK1,sK2) | ~r1_tarski(k2_pre_topc(sK1,k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,sK7(sK1,sK2,k1_xboole_0))),k8_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(sK1,sK2,k1_xboole_0)))) | ~spl10_45),
% 2.66/0.75    inference(superposition,[],[f1845,f157])).
% 2.66/0.75  fof(f1845,plain,(
% 2.66/0.75    ( ! [X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v5_pre_topc(k1_xboole_0,X1,sK2) | ~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0))))) ) | ~spl10_45),
% 2.66/0.75    inference(avatar_component_clause,[],[f1844])).
% 2.66/0.75  fof(f2575,plain,(
% 2.66/0.75    ~spl10_6 | ~spl10_8 | spl10_60),
% 2.66/0.75    inference(avatar_contradiction_clause,[],[f2574])).
% 2.66/0.75  fof(f2574,plain,(
% 2.66/0.75    $false | (~spl10_6 | ~spl10_8 | spl10_60)),
% 2.66/0.75    inference(resolution,[],[f2572,f2278])).
% 2.66/0.75  fof(f2278,plain,(
% 2.66/0.75    v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0) | (~spl10_6 | ~spl10_8)),
% 2.66/0.75    inference(backward_demodulation,[],[f2159,f1847])).
% 2.66/0.75  fof(f1847,plain,(
% 2.66/0.75    k1_xboole_0 = k2_struct_0(sK2) | ~spl10_6),
% 2.66/0.75    inference(backward_demodulation,[],[f158,f1382])).
% 2.66/0.75  fof(f1382,plain,(
% 2.66/0.75    k1_xboole_0 = u1_struct_0(sK2) | ~spl10_6),
% 2.66/0.75    inference(backward_demodulation,[],[f158,f1164])).
% 2.66/0.75  fof(f1164,plain,(
% 2.66/0.75    k1_xboole_0 = k2_struct_0(sK2) | ~spl10_6),
% 2.66/0.75    inference(backward_demodulation,[],[f158,f783])).
% 2.66/0.75  fof(f783,plain,(
% 2.66/0.75    k1_xboole_0 = u1_struct_0(sK2) | ~spl10_6),
% 2.66/0.75    inference(backward_demodulation,[],[f158,f576])).
% 2.66/0.75  fof(f576,plain,(
% 2.66/0.75    k1_xboole_0 = k2_struct_0(sK2) | ~spl10_6),
% 2.66/0.75    inference(avatar_component_clause,[],[f574])).
% 2.66/0.75  fof(f574,plain,(
% 2.66/0.75    spl10_6 <=> k1_xboole_0 = k2_struct_0(sK2)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 2.66/0.75  fof(f158,plain,(
% 2.66/0.75    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 2.66/0.75    inference(resolution,[],[f156,f92])).
% 2.66/0.75  fof(f92,plain,(
% 2.66/0.75    l1_pre_topc(sK2)),
% 2.66/0.75    inference(cnf_transformation,[],[f57])).
% 2.66/0.75  fof(f2159,plain,(
% 2.66/0.75    v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k2_struct_0(sK2)) | ~spl10_8),
% 2.66/0.75    inference(backward_demodulation,[],[f162,f583])).
% 2.66/0.75  fof(f162,plain,(
% 2.66/0.75    v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2))),
% 2.66/0.75    inference(backward_demodulation,[],[f159,f158])).
% 2.66/0.75  fof(f159,plain,(
% 2.66/0.75    v1_funct_2(sK3,k2_struct_0(sK1),u1_struct_0(sK2))),
% 2.66/0.75    inference(backward_demodulation,[],[f94,f157])).
% 2.66/0.75  fof(f94,plain,(
% 2.66/0.75    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.66/0.75    inference(cnf_transformation,[],[f57])).
% 2.66/0.75  fof(f2572,plain,(
% 2.66/0.75    ~v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0) | spl10_60),
% 2.66/0.75    inference(avatar_component_clause,[],[f2570])).
% 2.66/0.75  fof(f2573,plain,(
% 2.66/0.75    spl10_58 | spl10_59 | ~spl10_15 | ~spl10_23 | ~spl10_60 | ~spl10_44),
% 2.66/0.75    inference(avatar_split_clause,[],[f2559,f1840,f2570,f1079,f931,f2566,f2562])).
% 2.66/0.75  fof(f1840,plain,(
% 2.66/0.75    spl10_44 <=> ! [X1] : (m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v5_pre_topc(k1_xboole_0,X1,sK2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 2.66/0.75  fof(f2559,plain,(
% 2.66/0.75    ~v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v5_pre_topc(k1_xboole_0,sK1,sK2) | m1_subset_1(sK7(sK1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl10_44),
% 2.66/0.75    inference(superposition,[],[f1841,f157])).
% 2.66/0.75  fof(f1841,plain,(
% 2.66/0.75    ( ! [X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v5_pre_topc(k1_xboole_0,X1,sK2) | m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) ) | ~spl10_44),
% 2.66/0.75    inference(avatar_component_clause,[],[f1840])).
% 2.66/0.75  fof(f2472,plain,(
% 2.66/0.75    ~spl10_5 | ~spl10_6),
% 2.66/0.75    inference(avatar_contradiction_clause,[],[f2468])).
% 2.66/0.75  fof(f2468,plain,(
% 2.66/0.75    $false | (~spl10_5 | ~spl10_6)),
% 2.66/0.75    inference(resolution,[],[f2300,f98])).
% 2.66/0.75  fof(f2300,plain,(
% 2.66/0.75    ( ! [X1] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,k1_relat_1(k1_xboole_0)))) ) | (~spl10_5 | ~spl10_6)),
% 2.66/0.75    inference(forward_demodulation,[],[f2261,f149])).
% 2.66/0.75  fof(f2261,plain,(
% 2.66/0.75    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0),k2_zfmisc_1(X1,k1_relat_1(k1_xboole_0)))) ) | (~spl10_5 | ~spl10_6)),
% 2.66/0.75    inference(backward_demodulation,[],[f560,f1847])).
% 2.66/0.75  fof(f560,plain,(
% 2.66/0.75    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X1,k1_relat_1(k1_xboole_0)))) ) | ~spl10_5),
% 2.66/0.75    inference(avatar_component_clause,[],[f559])).
% 2.66/0.75  fof(f559,plain,(
% 2.66/0.75    spl10_5 <=> ! [X1] : ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X1,k1_relat_1(k1_xboole_0)))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 2.66/0.75  fof(f2155,plain,(
% 2.66/0.75    spl10_6 | spl10_14),
% 2.66/0.75    inference(avatar_split_clause,[],[f2060,f712,f574])).
% 2.66/0.75  fof(f712,plain,(
% 2.66/0.75    spl10_14 <=> ! [X1] : (~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) | ~l1_pre_topc(X1) | sP0(X1,sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 2.66/0.75  fof(f2060,plain,(
% 2.66/0.75    ( ! [X1] : (~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | sP0(X1,sK3,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~l1_pre_topc(X1)) )),
% 2.66/0.75    inference(forward_demodulation,[],[f2059,f158])).
% 2.66/0.75  fof(f2059,plain,(
% 2.66/0.75    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(sK2)) | sP0(X1,sK3,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~l1_pre_topc(X1)) )),
% 2.66/0.75    inference(forward_demodulation,[],[f2056,f158])).
% 2.66/0.75  fof(f2056,plain,(
% 2.66/0.75    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(sK2)) | sP0(X1,sK3,sK2) | k1_xboole_0 = k2_struct_0(sK2) | ~l1_pre_topc(X1)) )),
% 2.66/0.75    inference(resolution,[],[f586,f92])).
% 2.66/0.75  fof(f586,plain,(
% 2.66/0.75    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) | sP0(X1,sK3,X0) | k1_xboole_0 = k2_struct_0(X0) | ~l1_pre_topc(X1)) )),
% 2.66/0.75    inference(resolution,[],[f110,f93])).
% 2.66/0.75  fof(f93,plain,(
% 2.66/0.75    v1_funct_1(sK3)),
% 2.66/0.75    inference(cnf_transformation,[],[f57])).
% 2.66/0.75  fof(f110,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | sP0(X0,X2,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f53])).
% 2.66/0.75  fof(f53,plain,(
% 2.66/0.75    ! [X0] : (! [X1] : (! [X2] : (sP0(X0,X2,X1) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.66/0.75    inference(definition_folding,[],[f35,f52])).
% 2.66/0.75  fof(f52,plain,(
% 2.66/0.75    ! [X0,X2,X1] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~sP0(X0,X2,X1))),
% 2.66/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.66/0.75  fof(f35,plain,(
% 2.66/0.75    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.66/0.75    inference(flattening,[],[f34])).
% 2.66/0.75  fof(f34,plain,(
% 2.66/0.75    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.66/0.75    inference(ennf_transformation,[],[f21])).
% 2.66/0.75  fof(f21,axiom,(
% 2.66/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).
% 2.66/0.75  fof(f2154,plain,(
% 2.66/0.75    spl10_1 | ~spl10_2),
% 2.66/0.75    inference(avatar_split_clause,[],[f2039,f195,f191])).
% 2.66/0.75  fof(f191,plain,(
% 2.66/0.75    spl10_1 <=> sK3 = k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 2.66/0.75  fof(f195,plain,(
% 2.66/0.75    spl10_2 <=> r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),sK3)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 2.66/0.75  fof(f2039,plain,(
% 2.66/0.75    ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),sK3) | sK3 = k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))),
% 2.66/0.75    inference(resolution,[],[f161,f166])).
% 2.66/0.75  fof(f166,plain,(
% 2.66/0.75    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(X4)) | ~r1_tarski(X4,X5) | X4 = X5) )),
% 2.66/0.75    inference(resolution,[],[f131,f135])).
% 2.66/0.75  fof(f161,plain,(
% 2.66/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))),
% 2.66/0.75    inference(backward_demodulation,[],[f160,f158])).
% 2.66/0.75  fof(f160,plain,(
% 2.66/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2))))),
% 2.66/0.75    inference(backward_demodulation,[],[f95,f157])).
% 2.66/0.75  fof(f95,plain,(
% 2.66/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.66/0.75    inference(cnf_transformation,[],[f57])).
% 2.66/0.75  fof(f2153,plain,(
% 2.66/0.75    spl10_43),
% 2.66/0.75    inference(avatar_contradiction_clause,[],[f2151])).
% 2.66/0.75  fof(f2151,plain,(
% 2.66/0.75    $false | spl10_43),
% 2.66/0.75    inference(resolution,[],[f1727,f161])).
% 2.66/0.75  fof(f1727,plain,(
% 2.66/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) | spl10_43),
% 2.66/0.75    inference(resolution,[],[f1588,f145])).
% 2.66/0.75  fof(f1588,plain,(
% 2.66/0.75    ~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(k2_struct_0(sK1))) | spl10_43),
% 2.66/0.75    inference(avatar_component_clause,[],[f1586])).
% 2.66/0.75  fof(f1586,plain,(
% 2.66/0.75    spl10_43 <=> m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(k2_struct_0(sK1)))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).
% 2.66/0.75  fof(f2137,plain,(
% 2.66/0.75    spl10_47),
% 2.66/0.75    inference(avatar_contradiction_clause,[],[f2135])).
% 2.66/0.75  fof(f2135,plain,(
% 2.66/0.75    $false | spl10_47),
% 2.66/0.75    inference(resolution,[],[f2014,f161])).
% 2.66/0.75  fof(f2014,plain,(
% 2.66/0.75    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) | spl10_47),
% 2.66/0.75    inference(avatar_component_clause,[],[f2012])).
% 2.66/0.75  fof(f2012,plain,(
% 2.66/0.75    spl10_47 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).
% 2.66/0.75  fof(f2016,plain,(
% 2.66/0.75    ~spl10_47 | spl10_29 | ~spl10_23 | ~spl10_30 | ~spl10_14),
% 2.66/0.75    inference(avatar_split_clause,[],[f1109,f712,f1117,f1079,f1113,f2012])).
% 2.66/0.75  fof(f1113,plain,(
% 2.66/0.75    spl10_29 <=> sP0(sK1,sK3,sK2)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 2.66/0.75  fof(f1117,plain,(
% 2.66/0.75    spl10_30 <=> v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 2.66/0.75  fof(f1109,plain,(
% 2.66/0.75    ~v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) | ~l1_pre_topc(sK1) | sP0(sK1,sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) | ~spl10_14),
% 2.66/0.75    inference(superposition,[],[f713,f157])).
% 2.66/0.75  fof(f713,plain,(
% 2.66/0.75    ( ! [X1] : (~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) | ~l1_pre_topc(X1) | sP0(X1,sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2))))) ) | ~spl10_14),
% 2.66/0.75    inference(avatar_component_clause,[],[f712])).
% 2.66/0.75  fof(f1846,plain,(
% 2.66/0.75    spl10_45 | ~spl10_4 | ~spl10_6 | ~spl10_8 | ~spl10_20),
% 2.66/0.75    inference(avatar_split_clause,[],[f1402,f1027,f582,f574,f484,f1844])).
% 2.66/0.75  fof(f1027,plain,(
% 2.66/0.75    spl10_20 <=> ! [X1] : (~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v5_pre_topc(sK3,X1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 2.66/0.75  fof(f1402,plain,(
% 2.66/0.75    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X1,sK2) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1)) ) | (~spl10_6 | ~spl10_8 | ~spl10_20)),
% 2.66/0.75    inference(forward_demodulation,[],[f1401,f149])).
% 2.66/0.75  fof(f1401,plain,(
% 2.66/0.75    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X1,sK2) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1)) ) | (~spl10_6 | ~spl10_8 | ~spl10_20)),
% 2.66/0.75    inference(forward_demodulation,[],[f1400,f1164])).
% 2.66/0.75  fof(f1400,plain,(
% 2.66/0.75    ( ! [X1] : (~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X1,sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1)) ) | (~spl10_6 | ~spl10_8 | ~spl10_20)),
% 2.66/0.75    inference(forward_demodulation,[],[f1394,f1164])).
% 2.66/0.75  fof(f1394,plain,(
% 2.66/0.75    ( ! [X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X1,sK2) | ~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1)) ) | (~spl10_6 | ~spl10_8 | ~spl10_20)),
% 2.66/0.75    inference(backward_demodulation,[],[f1371,f1164])).
% 2.66/0.75  fof(f1371,plain,(
% 2.66/0.75    ( ! [X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k2_struct_0(sK2)) | v5_pre_topc(k1_xboole_0,X1,sK2) | ~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1)) ) | (~spl10_8 | ~spl10_20)),
% 2.66/0.75    inference(forward_demodulation,[],[f1370,f583])).
% 2.66/0.75  fof(f1370,plain,(
% 2.66/0.75    ( ! [X1] : (v5_pre_topc(k1_xboole_0,X1,sK2) | ~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))) ) | (~spl10_8 | ~spl10_20)),
% 2.66/0.75    inference(forward_demodulation,[],[f1369,f583])).
% 2.66/0.75  fof(f1369,plain,(
% 2.66/0.75    ( ! [X1] : (~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,sK7(X1,sK2,k1_xboole_0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k1_xboole_0,k2_pre_topc(sK2,sK7(X1,sK2,k1_xboole_0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v5_pre_topc(sK3,X1,sK2) | ~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))) ) | (~spl10_8 | ~spl10_20)),
% 2.66/0.75    inference(forward_demodulation,[],[f1333,f583])).
% 2.66/0.75  fof(f1333,plain,(
% 2.66/0.75    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v5_pre_topc(sK3,X1,sK2) | ~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))) ) | (~spl10_8 | ~spl10_20)),
% 2.66/0.75    inference(backward_demodulation,[],[f1028,f583])).
% 2.66/0.75  fof(f1028,plain,(
% 2.66/0.75    ( ! [X1] : (~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v5_pre_topc(sK3,X1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))) ) | ~spl10_20),
% 2.66/0.75    inference(avatar_component_clause,[],[f1027])).
% 2.66/0.75  fof(f1842,plain,(
% 2.66/0.75    spl10_44 | ~spl10_4 | ~spl10_6 | ~spl10_8 | ~spl10_18),
% 2.66/0.75    inference(avatar_split_clause,[],[f1399,f946,f582,f574,f484,f1840])).
% 2.66/0.75  fof(f946,plain,(
% 2.66/0.75    spl10_18 <=> ! [X1] : (m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v5_pre_topc(sK3,X1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)))),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 2.66/0.75  fof(f1399,plain,(
% 2.66/0.75    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X1,sK2) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1)) ) | (~spl10_6 | ~spl10_8 | ~spl10_18)),
% 2.66/0.75    inference(forward_demodulation,[],[f1398,f149])).
% 2.66/0.75  fof(f1398,plain,(
% 2.66/0.75    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X1,sK2) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1)) ) | (~spl10_6 | ~spl10_8 | ~spl10_18)),
% 2.66/0.75    inference(forward_demodulation,[],[f1397,f1164])).
% 2.66/0.75  fof(f1397,plain,(
% 2.66/0.75    ( ! [X1] : (m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X1,sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1)) ) | (~spl10_6 | ~spl10_8 | ~spl10_18)),
% 2.66/0.75    inference(forward_demodulation,[],[f1393,f1164])).
% 2.66/0.75  fof(f1393,plain,(
% 2.66/0.75    ( ! [X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X1,sK2) | m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1)) ) | (~spl10_6 | ~spl10_8 | ~spl10_18)),
% 2.66/0.75    inference(backward_demodulation,[],[f1363,f1164])).
% 2.66/0.75  fof(f1363,plain,(
% 2.66/0.75    ( ! [X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X1),k2_struct_0(sK2)) | v5_pre_topc(k1_xboole_0,X1,sK2) | m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1)) ) | (~spl10_8 | ~spl10_18)),
% 2.66/0.75    inference(forward_demodulation,[],[f1362,f583])).
% 2.66/0.75  fof(f1362,plain,(
% 2.66/0.75    ( ! [X1] : (v5_pre_topc(k1_xboole_0,X1,sK2) | m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))) ) | (~spl10_8 | ~spl10_18)),
% 2.66/0.75    inference(forward_demodulation,[],[f1361,f583])).
% 2.66/0.75  fof(f1361,plain,(
% 2.66/0.75    ( ! [X1] : (m1_subset_1(sK7(X1,sK2,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v5_pre_topc(sK3,X1,sK2) | ~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))) ) | (~spl10_8 | ~spl10_18)),
% 2.66/0.75    inference(forward_demodulation,[],[f1330,f583])).
% 2.66/0.75  fof(f1330,plain,(
% 2.66/0.75    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v5_pre_topc(sK3,X1,sK2) | ~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))) ) | (~spl10_8 | ~spl10_18)),
% 2.66/0.75    inference(backward_demodulation,[],[f947,f583])).
% 2.66/0.75  fof(f947,plain,(
% 2.66/0.75    ( ! [X1] : (m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v5_pre_topc(sK3,X1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2))) ) | ~spl10_18),
% 2.66/0.75    inference(avatar_component_clause,[],[f946])).
% 2.66/0.75  fof(f1595,plain,(
% 2.66/0.75    spl10_42),
% 2.66/0.75    inference(avatar_contradiction_clause,[],[f1590])).
% 2.66/0.75  fof(f1590,plain,(
% 2.66/0.75    $false | spl10_42),
% 2.66/0.75    inference(resolution,[],[f1584,f89])).
% 2.66/0.75  fof(f89,plain,(
% 2.66/0.75    v1_tdlat_3(sK1)),
% 2.66/0.75    inference(cnf_transformation,[],[f57])).
% 2.66/0.75  fof(f1584,plain,(
% 2.66/0.75    ~v1_tdlat_3(sK1) | spl10_42),
% 2.66/0.75    inference(avatar_component_clause,[],[f1582])).
% 2.66/0.75  fof(f1589,plain,(
% 2.66/0.75    ~spl10_15 | ~spl10_23 | ~spl10_42 | ~spl10_43 | spl10_36),
% 2.66/0.75    inference(avatar_split_clause,[],[f1580,f1153,f1586,f1582,f1079,f931])).
% 2.66/0.75  fof(f1153,plain,(
% 2.66/0.75    spl10_36 <=> v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 2.66/0.75  fof(f1580,plain,(
% 2.66/0.75    ~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(k2_struct_0(sK1))) | ~v1_tdlat_3(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl10_36),
% 2.66/0.75    inference(forward_demodulation,[],[f1579,f157])).
% 2.66/0.75  fof(f1579,plain,(
% 2.66/0.75    ~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_tdlat_3(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl10_36),
% 2.66/0.75    inference(resolution,[],[f1155,f114])).
% 2.66/0.75  fof(f114,plain,(
% 2.66/0.75    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f65])).
% 2.66/0.75  fof(f65,plain,(
% 2.66/0.75    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).
% 2.66/0.75  fof(f64,plain,(
% 2.66/0.75    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.66/0.75    introduced(choice_axiom,[])).
% 2.66/0.75  fof(f63,plain,(
% 2.66/0.75    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.75    inference(rectify,[],[f62])).
% 2.66/0.75  fof(f62,plain,(
% 2.66/0.75    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.75    inference(nnf_transformation,[],[f39])).
% 2.66/0.75  fof(f39,plain,(
% 2.66/0.75    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.75    inference(flattening,[],[f38])).
% 2.66/0.75  fof(f38,plain,(
% 2.66/0.75    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.66/0.75    inference(ennf_transformation,[],[f24])).
% 2.66/0.75  fof(f24,axiom,(
% 2.66/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 2.66/0.75  fof(f1155,plain,(
% 2.66/0.75    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1) | spl10_36),
% 2.66/0.75    inference(avatar_component_clause,[],[f1153])).
% 2.66/0.75  fof(f1308,plain,(
% 2.66/0.75    ~spl10_35),
% 2.66/0.75    inference(avatar_contradiction_clause,[],[f1306])).
% 2.66/0.75  fof(f1306,plain,(
% 2.66/0.75    $false | ~spl10_35),
% 2.66/0.75    inference(resolution,[],[f1151,f96])).
% 2.66/0.75  fof(f1151,plain,(
% 2.66/0.75    v5_pre_topc(sK3,sK1,sK2) | ~spl10_35),
% 2.66/0.75    inference(avatar_component_clause,[],[f1149])).
% 2.66/0.75  fof(f1149,plain,(
% 2.66/0.75    spl10_35 <=> v5_pre_topc(sK3,sK1,sK2)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).
% 2.66/0.75  fof(f1281,plain,(
% 2.66/0.75    ~spl10_1 | ~spl10_6 | spl10_10),
% 2.66/0.75    inference(avatar_contradiction_clause,[],[f1278])).
% 2.66/0.75  fof(f1278,plain,(
% 2.66/0.75    $false | (~spl10_1 | ~spl10_6 | spl10_10)),
% 2.66/0.75    inference(resolution,[],[f1181,f97])).
% 2.66/0.75  fof(f97,plain,(
% 2.66/0.75    v1_xboole_0(k1_xboole_0)),
% 2.66/0.75    inference(cnf_transformation,[],[f3])).
% 2.66/0.75  fof(f3,axiom,(
% 2.66/0.75    v1_xboole_0(k1_xboole_0)),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.66/0.75  fof(f1181,plain,(
% 2.66/0.75    ~v1_xboole_0(k1_xboole_0) | (~spl10_1 | ~spl10_6 | spl10_10)),
% 2.66/0.75    inference(backward_demodulation,[],[f629,f1175])).
% 2.66/0.75  fof(f1175,plain,(
% 2.66/0.75    k1_xboole_0 = sK3 | (~spl10_1 | ~spl10_6)),
% 2.66/0.75    inference(forward_demodulation,[],[f1166,f149])).
% 2.66/0.75  fof(f1166,plain,(
% 2.66/0.75    sK3 = k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0) | (~spl10_1 | ~spl10_6)),
% 2.66/0.75    inference(backward_demodulation,[],[f193,f1164])).
% 2.66/0.75  fof(f193,plain,(
% 2.66/0.75    sK3 = k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)) | ~spl10_1),
% 2.66/0.75    inference(avatar_component_clause,[],[f191])).
% 2.66/0.75  fof(f629,plain,(
% 2.66/0.75    ~v1_xboole_0(sK3) | spl10_10),
% 2.66/0.75    inference(resolution,[],[f603,f123])).
% 2.66/0.75  fof(f123,plain,(
% 2.66/0.75    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f77])).
% 2.66/0.75  fof(f77,plain,(
% 2.66/0.75    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.66/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f75,f76])).
% 2.66/0.75  fof(f76,plain,(
% 2.66/0.75    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 2.66/0.75    introduced(choice_axiom,[])).
% 2.66/0.75  fof(f75,plain,(
% 2.66/0.75    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.66/0.75    inference(rectify,[],[f74])).
% 2.66/0.75  fof(f74,plain,(
% 2.66/0.75    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.66/0.75    inference(nnf_transformation,[],[f1])).
% 2.66/0.75  fof(f1,axiom,(
% 2.66/0.75    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.66/0.75  fof(f603,plain,(
% 2.66/0.75    r2_hidden(sK9(sK3,k1_xboole_0),sK3) | spl10_10),
% 2.66/0.75    inference(resolution,[],[f596,f133])).
% 2.66/0.75  fof(f133,plain,(
% 2.66/0.75    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK9(X0,X1),X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f84])).
% 2.66/0.75  fof(f84,plain,(
% 2.66/0.75    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.66/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f82,f83])).
% 2.66/0.75  % (7934)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.66/0.75  fof(f83,plain,(
% 2.66/0.75    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 2.66/0.75    introduced(choice_axiom,[])).
% 2.66/0.75  fof(f82,plain,(
% 2.66/0.75    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.66/0.75    inference(rectify,[],[f81])).
% 2.66/0.75  fof(f81,plain,(
% 2.66/0.75    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.66/0.75    inference(nnf_transformation,[],[f47])).
% 2.66/0.75  fof(f47,plain,(
% 2.66/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.66/0.75    inference(ennf_transformation,[],[f2])).
% 2.66/0.75  fof(f2,axiom,(
% 2.66/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.66/0.75  fof(f596,plain,(
% 2.66/0.75    ~r1_tarski(sK3,k1_xboole_0) | spl10_10),
% 2.66/0.75    inference(avatar_component_clause,[],[f594])).
% 2.66/0.75  fof(f594,plain,(
% 2.66/0.75    spl10_10 <=> r1_tarski(sK3,k1_xboole_0)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 2.66/0.75  fof(f1156,plain,(
% 2.66/0.75    spl10_35 | ~spl10_36 | ~spl10_29),
% 2.66/0.75    inference(avatar_split_clause,[],[f1147,f1113,f1153,f1149])).
% 2.66/0.75  fof(f1147,plain,(
% 2.66/0.75    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1) | v5_pre_topc(sK3,sK1,sK2) | ~spl10_29),
% 2.66/0.75    inference(forward_demodulation,[],[f1146,f157])).
% 2.66/0.75  fof(f1146,plain,(
% 2.66/0.75    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1) | v5_pre_topc(sK3,sK1,sK2) | ~spl10_29),
% 2.66/0.75    inference(forward_demodulation,[],[f1144,f158])).
% 2.66/0.75  fof(f1144,plain,(
% 2.66/0.75    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4(sK1,sK3,sK2)),sK1) | v5_pre_topc(sK3,sK1,sK2) | ~spl10_29),
% 2.66/0.75    inference(resolution,[],[f1115,f109])).
% 2.66/0.75  fof(f109,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK4(X0,X1,X2)),X0) | v5_pre_topc(X1,X0,X2)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f61])).
% 2.66/0.75  fof(f61,plain,(
% 2.66/0.75    ! [X0,X1,X2] : (((v5_pre_topc(X1,X0,X2) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK4(X0,X1,X2)),X0) & v3_pre_topc(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~v5_pre_topc(X1,X0,X2))) | ~sP0(X0,X1,X2))),
% 2.66/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).
% 2.66/0.75  fof(f60,plain,(
% 2.66/0.75    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK4(X0,X1,X2)),X0) & v3_pre_topc(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 2.66/0.75    introduced(choice_axiom,[])).
% 2.66/0.75  fof(f59,plain,(
% 2.66/0.75    ! [X0,X1,X2] : (((v5_pre_topc(X1,X0,X2) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~v5_pre_topc(X1,X0,X2))) | ~sP0(X0,X1,X2))),
% 2.66/0.75    inference(rectify,[],[f58])).
% 2.66/0.75  fof(f58,plain,(
% 2.66/0.75    ! [X0,X2,X1] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~sP0(X0,X2,X1))),
% 2.66/0.75    inference(nnf_transformation,[],[f52])).
% 2.66/0.75  fof(f1115,plain,(
% 2.66/0.75    sP0(sK1,sK3,sK2) | ~spl10_29),
% 2.66/0.75    inference(avatar_component_clause,[],[f1113])).
% 2.66/0.75  fof(f1142,plain,(
% 2.66/0.75    spl10_30),
% 2.66/0.75    inference(avatar_contradiction_clause,[],[f1141])).
% 2.66/0.75  fof(f1141,plain,(
% 2.66/0.75    $false | spl10_30),
% 2.66/0.75    inference(resolution,[],[f1119,f162])).
% 2.66/0.75  fof(f1119,plain,(
% 2.66/0.75    ~v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) | spl10_30),
% 2.66/0.75    inference(avatar_component_clause,[],[f1117])).
% 2.66/0.75  fof(f1105,plain,(
% 2.66/0.75    spl10_23),
% 2.66/0.75    inference(avatar_contradiction_clause,[],[f1104])).
% 2.66/0.75  fof(f1104,plain,(
% 2.66/0.75    $false | spl10_23),
% 2.66/0.75    inference(resolution,[],[f1081,f90])).
% 2.66/0.75  fof(f1081,plain,(
% 2.66/0.75    ~l1_pre_topc(sK1) | spl10_23),
% 2.66/0.75    inference(avatar_component_clause,[],[f1079])).
% 2.66/0.75  fof(f1029,plain,(
% 2.66/0.75    ~spl10_17 | spl10_20),
% 2.66/0.75    inference(avatar_split_clause,[],[f1025,f1027,f942])).
% 2.66/0.75  fof(f942,plain,(
% 2.66/0.75    spl10_17 <=> v2_pre_topc(sK2)),
% 2.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 2.66/0.75  fof(f1025,plain,(
% 2.66/0.75    ( ! [X1] : (~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3)))) | ~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | v5_pre_topc(sK3,X1,sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.66/0.75    inference(forward_demodulation,[],[f1024,f158])).
% 2.66/0.75  fof(f1024,plain,(
% 2.66/0.75    ( ! [X1] : (~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | v5_pre_topc(sK3,X1,sK2) | ~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3)))) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.66/0.75    inference(forward_demodulation,[],[f1023,f158])).
% 2.66/0.75  fof(f1023,plain,(
% 2.66/0.75    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(sK2)) | v5_pre_topc(sK3,X1,sK2) | ~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3)))) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.66/0.75    inference(forward_demodulation,[],[f1015,f158])).
% 2.66/0.75  fof(f1015,plain,(
% 2.66/0.75    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(sK2)) | v5_pre_topc(sK3,X1,sK2) | ~r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),sK3,sK7(X1,sK2,sK3))),k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK7(X1,sK2,sK3)))) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.66/0.75    inference(resolution,[],[f679,f92])).
% 2.66/0.75  fof(f679,plain,(
% 2.66/0.75    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK3,X0,X1) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,sK7(X0,X1,sK3))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k2_pre_topc(X1,sK7(X0,X1,sK3)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.66/0.75    inference(resolution,[],[f122,f93])).
% 2.66/0.75  fof(f122,plain,(
% 2.66/0.75    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.66/0.75    inference(cnf_transformation,[],[f73])).
% 2.66/0.75  fof(f73,plain,(
% 2.66/0.75    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2)))) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f71,f72])).
% 2.66/0.75  fof(f72,plain,(
% 2.66/0.75    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2)))) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.66/0.75    introduced(choice_axiom,[])).
% 2.66/0.75  fof(f71,plain,(
% 2.66/0.75    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.75    inference(rectify,[],[f70])).
% 2.66/0.75  fof(f70,plain,(
% 2.66/0.75    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.75    inference(nnf_transformation,[],[f43])).
% 2.66/0.76  fof(f43,plain,(
% 2.66/0.76    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.66/0.76    inference(flattening,[],[f42])).
% 2.66/0.76  fof(f42,plain,(
% 2.66/0.76    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.66/0.76    inference(ennf_transformation,[],[f22])).
% 2.66/0.76  fof(f22,axiom,(
% 2.66/0.76    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 2.66/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).
% 2.66/0.76  fof(f954,plain,(
% 2.66/0.76    spl10_17),
% 2.66/0.76    inference(avatar_contradiction_clause,[],[f952])).
% 2.66/0.76  fof(f952,plain,(
% 2.66/0.76    $false | spl10_17),
% 2.66/0.76    inference(resolution,[],[f944,f91])).
% 2.66/0.76  fof(f91,plain,(
% 2.66/0.76    v2_pre_topc(sK2)),
% 2.66/0.76    inference(cnf_transformation,[],[f57])).
% 2.66/0.76  fof(f944,plain,(
% 2.66/0.76    ~v2_pre_topc(sK2) | spl10_17),
% 2.66/0.76    inference(avatar_component_clause,[],[f942])).
% 2.66/0.76  fof(f951,plain,(
% 2.66/0.76    spl10_15),
% 2.66/0.76    inference(avatar_contradiction_clause,[],[f949])).
% 2.66/0.76  fof(f949,plain,(
% 2.66/0.76    $false | spl10_15),
% 2.66/0.76    inference(resolution,[],[f933,f88])).
% 2.66/0.76  fof(f88,plain,(
% 2.66/0.76    v2_pre_topc(sK1)),
% 2.66/0.76    inference(cnf_transformation,[],[f57])).
% 2.66/0.76  fof(f933,plain,(
% 2.66/0.76    ~v2_pre_topc(sK1) | spl10_15),
% 2.66/0.76    inference(avatar_component_clause,[],[f931])).
% 2.66/0.76  fof(f948,plain,(
% 2.66/0.76    ~spl10_17 | spl10_18),
% 2.66/0.76    inference(avatar_split_clause,[],[f940,f946,f942])).
% 2.66/0.76  fof(f940,plain,(
% 2.66/0.76    ( ! [X1] : (m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(k2_struct_0(sK2))) | ~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | v5_pre_topc(sK3,X1,sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.66/0.76    inference(forward_demodulation,[],[f939,f158])).
% 2.66/0.76  fof(f939,plain,(
% 2.66/0.76    ( ! [X1] : (~v1_funct_2(sK3,u1_struct_0(X1),k2_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | v5_pre_topc(sK3,X1,sK2) | m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.66/0.76    inference(forward_demodulation,[],[f938,f158])).
% 2.66/0.76  fof(f938,plain,(
% 2.66/0.76    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(sK2)) | v5_pre_topc(sK3,X1,sK2) | m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.66/0.76    inference(forward_demodulation,[],[f926,f158])).
% 2.66/0.76  fof(f926,plain,(
% 2.66/0.76    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(sK2)) | v5_pre_topc(sK3,X1,sK2) | m1_subset_1(sK7(X1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.66/0.76    inference(resolution,[],[f639,f92])).
% 2.66/0.76  fof(f639,plain,(
% 2.66/0.76    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK3,X0,X1) | m1_subset_1(sK7(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.66/0.76    inference(resolution,[],[f121,f93])).
% 2.66/0.76  fof(f121,plain,(
% 2.66/0.76    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.66/0.76    inference(cnf_transformation,[],[f73])).
% 2.66/0.76  fof(f602,plain,(
% 2.66/0.76    spl10_9),
% 2.66/0.76    inference(avatar_contradiction_clause,[],[f599])).
% 2.66/0.76  fof(f599,plain,(
% 2.66/0.76    $false | spl10_9),
% 2.66/0.76    inference(resolution,[],[f592,f98])).
% 2.66/0.76  fof(f592,plain,(
% 2.66/0.76    ~r1_tarski(k1_xboole_0,sK3) | spl10_9),
% 2.66/0.76    inference(avatar_component_clause,[],[f590])).
% 2.66/0.76  fof(f590,plain,(
% 2.66/0.76    spl10_9 <=> r1_tarski(k1_xboole_0,sK3)),
% 2.66/0.76    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 2.66/0.76  fof(f598,plain,(
% 2.66/0.76    ~spl10_10 | ~spl10_9 | spl10_8),
% 2.66/0.76    inference(avatar_split_clause,[],[f588,f582,f590,f594])).
% 2.66/0.76  fof(f588,plain,(
% 2.66/0.76    ~r1_tarski(k1_xboole_0,sK3) | ~r1_tarski(sK3,k1_xboole_0) | spl10_8),
% 2.66/0.76    inference(extensionality_resolution,[],[f131,f584])).
% 2.66/0.76  fof(f584,plain,(
% 2.66/0.76    k1_xboole_0 != sK3 | spl10_8),
% 2.66/0.76    inference(avatar_component_clause,[],[f582])).
% 2.66/0.76  fof(f561,plain,(
% 2.66/0.76    spl10_5 | ~spl10_4 | spl10_2),
% 2.66/0.76    inference(avatar_split_clause,[],[f557,f195,f484,f559])).
% 2.66/0.76  fof(f557,plain,(
% 2.66/0.76    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X1,k1_relat_1(k1_xboole_0)))) ) | spl10_2),
% 2.66/0.76    inference(forward_demodulation,[],[f555,f150])).
% 2.66/0.76  fof(f555,plain,(
% 2.66/0.76    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X1,k1_relat_1(k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | spl10_2),
% 2.66/0.76    inference(superposition,[],[f549,f140])).
% 2.66/0.76  fof(f549,plain,(
% 2.66/0.76    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X0,k1_relset_1(k1_xboole_0,X1,k1_xboole_0)))) ) | spl10_2),
% 2.66/0.76    inference(resolution,[],[f466,f151])).
% 2.66/0.76  fof(f466,plain,(
% 2.66/0.76    ( ! [X6,X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X8,k1_relset_1(k1_xboole_0,X6,X7)))) ) | spl10_2),
% 2.66/0.76    inference(duplicate_literal_removal,[],[f465])).
% 2.66/0.76  fof(f465,plain,(
% 2.66/0.76    ( ! [X6,X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X8,k1_relset_1(k1_xboole_0,X6,X7))) | ~m1_subset_1(X7,k1_zfmisc_1(k1_xboole_0))) ) | spl10_2),
% 2.66/0.76    inference(forward_demodulation,[],[f459,f150])).
% 2.66/0.76  fof(f459,plain,(
% 2.66/0.76    ( ! [X6,X8,X7] : (~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X8,k1_relset_1(k1_xboole_0,X6,X7))) | ~m1_subset_1(X7,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))) ) | spl10_2),
% 2.66/0.76    inference(superposition,[],[f375,f144])).
% 2.66/0.76  fof(f375,plain,(
% 2.66/0.76    ( ! [X6,X4,X7,X5] : (~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X6,k8_relset_1(k1_xboole_0,X5,X4,X7))) | ~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))) ) | spl10_2),
% 2.66/0.76    inference(forward_demodulation,[],[f371,f150])).
% 2.66/0.76  fof(f371,plain,(
% 2.66/0.76    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) | ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X6,k8_relset_1(k1_xboole_0,X5,X4,X7)))) ) | spl10_2),
% 2.66/0.76    inference(resolution,[],[f145,f291])).
% 2.66/0.76  fof(f291,plain,(
% 2.66/0.76    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X4,X5))) ) | spl10_2),
% 2.66/0.76    inference(resolution,[],[f250,f135])).
% 2.66/0.76  fof(f250,plain,(
% 2.66/0.76    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k2_zfmisc_1(X1,X0))) ) | spl10_2),
% 2.66/0.76    inference(resolution,[],[f246,f136])).
% 2.66/0.76  fof(f136,plain,(
% 2.66/0.76    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.66/0.76    inference(cnf_transformation,[],[f85])).
% 2.66/0.76  fof(f246,plain,(
% 2.66/0.76    ( ! [X0,X1] : (~m1_subset_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(X0,k1_xboole_0)) ) | spl10_2),
% 2.66/0.76    inference(resolution,[],[f245,f97])).
% 2.66/0.76  fof(f245,plain,(
% 2.66/0.76    ( ! [X6,X4,X5] : (~v1_xboole_0(X6) | ~r1_tarski(X5,X6) | ~m1_subset_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | spl10_2),
% 2.66/0.76    inference(resolution,[],[f223,f123])).
% 2.66/0.76  fof(f223,plain,(
% 2.66/0.76    ( ! [X2,X0,X1] : (r2_hidden(sK8(X1),X2) | ~m1_subset_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2)) ) | spl10_2),
% 2.66/0.76    inference(resolution,[],[f210,f132])).
% 2.66/0.76  fof(f132,plain,(
% 2.66/0.76    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.66/0.76    inference(cnf_transformation,[],[f84])).
% 2.66/0.76  fof(f210,plain,(
% 2.66/0.76    ( ! [X6,X5] : (r2_hidden(sK8(X6),X6) | ~m1_subset_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) ) | spl10_2),
% 2.66/0.76    inference(resolution,[],[f206,f124])).
% 2.66/0.76  fof(f124,plain,(
% 2.66/0.76    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) )),
% 2.66/0.76    inference(cnf_transformation,[],[f77])).
% 2.66/0.76  fof(f206,plain,(
% 2.66/0.76    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl10_2),
% 2.66/0.76    inference(resolution,[],[f205,f126])).
% 2.66/0.76  fof(f126,plain,(
% 2.66/0.76    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.66/0.76    inference(cnf_transformation,[],[f44])).
% 2.66/0.76  fof(f44,plain,(
% 2.66/0.76    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.66/0.76    inference(ennf_transformation,[],[f12])).
% 2.66/0.76  fof(f12,axiom,(
% 2.66/0.76    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.66/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 2.66/0.76  fof(f205,plain,(
% 2.66/0.76    ~v1_xboole_0(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) | spl10_2),
% 2.66/0.76    inference(resolution,[],[f201,f123])).
% 2.66/0.76  fof(f201,plain,(
% 2.66/0.76    r2_hidden(sK9(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),sK3),k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) | spl10_2),
% 2.66/0.76    inference(resolution,[],[f197,f133])).
% 2.66/0.76  fof(f197,plain,(
% 2.66/0.76    ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)),sK3) | spl10_2),
% 2.66/0.76    inference(avatar_component_clause,[],[f195])).
% 2.66/0.76  fof(f490,plain,(
% 2.66/0.76    spl10_4),
% 2.66/0.76    inference(avatar_contradiction_clause,[],[f488])).
% 2.66/0.76  fof(f488,plain,(
% 2.66/0.76    $false | spl10_4),
% 2.66/0.76    inference(resolution,[],[f486,f151])).
% 2.66/0.76  fof(f486,plain,(
% 2.66/0.76    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl10_4),
% 2.66/0.76    inference(avatar_component_clause,[],[f484])).
% 2.66/0.76  % SZS output end Proof for theBenchmark
% 2.66/0.76  % (7878)------------------------------
% 2.66/0.76  % (7878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.76  % (7878)Termination reason: Refutation
% 2.66/0.76  
% 2.66/0.76  % (7878)Memory used [KB]: 7419
% 2.66/0.76  % (7878)Time elapsed: 0.328 s
% 2.66/0.76  % (7878)------------------------------
% 2.66/0.76  % (7878)------------------------------
% 2.66/0.77  % (7860)Success in time 0.404 s
%------------------------------------------------------------------------------
