%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:38 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  322 (1973 expanded)
%              Number of leaves         :   60 ( 688 expanded)
%              Depth                    :   23
%              Number of atoms          : 1934 (10515 expanded)
%              Number of equality atoms :  110 (1121 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2996,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f144,f149,f154,f164,f169,f174,f179,f187,f231,f248,f277,f298,f303,f353,f363,f457,f511,f550,f594,f600,f631,f637,f690,f697,f920,f1042,f1057,f1063,f1129,f1204,f2931,f2955,f2963,f2971,f2979,f2987,f2995])).

fof(f2995,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_64
    | spl6_117 ),
    inference(avatar_contradiction_clause,[],[f2994])).

fof(f2994,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_64
    | spl6_117 ),
    inference(subsumption_resolution,[],[f2993,f163])).

fof(f163,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl6_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f2993,plain,
    ( v2_struct_0(sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_64
    | spl6_117 ),
    inference(subsumption_resolution,[],[f2992,f173])).

fof(f173,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f2992,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_64
    | spl6_117 ),
    inference(subsumption_resolution,[],[f2989,f1915])).

fof(f1915,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_64 ),
    inference(unit_resulting_resolution,[],[f352,f297,f1041,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f1041,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f1039])).

fof(f1039,plain,
    ( spl6_64
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f297,plain,
    ( l1_struct_0(sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl6_16
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f352,plain,
    ( l1_struct_0(sK2)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl6_24
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f2989,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_32
    | spl6_117 ),
    inference(resolution,[],[f2986,f535])).

fof(f535,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X1),u1_struct_0(X1),u1_struct_0(sK0))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f534,f463])).

fof(f463,plain,
    ( k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f143,f148,f153,f456,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f456,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl6_30
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f153,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f148,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f143,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f534,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(sK0))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f533,f476])).

fof(f476,plain,
    ( u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30 ),
    inference(forward_demodulation,[],[f464,f215])).

fof(f215,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f143,f148,f153,f168,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f135,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f135,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f134,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tmap_1)).

fof(f134,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f132,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f127,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f127,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK4(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK4(X0,X1,X2)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK4(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK4(X0,X1,X2)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f168,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl6_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f464,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f143,f148,f153,f456,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f533,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f532,f143])).

fof(f532,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f531,f148])).

fof(f531,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f530,f153])).

fof(f530,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f519,f456])).

fof(f519,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_32 ),
    inference(superposition,[],[f104,f510])).

fof(f510,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl6_32
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tmap_1)).

fof(f2986,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | spl6_117 ),
    inference(avatar_component_clause,[],[f2984])).

fof(f2984,plain,
    ( spl6_117
  <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f2987,plain,
    ( ~ spl6_117
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_13
    | ~ spl6_17
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41
    | ~ spl6_48
    | ~ spl6_68
    | ~ spl6_72
    | ~ spl6_77 ),
    inference(avatar_split_clause,[],[f2982,f1201,f1126,f1060,f694,f634,f597,f547,f300,f266,f166,f151,f146,f141,f2984])).

fof(f266,plain,
    ( spl6_13
  <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f300,plain,
    ( spl6_17
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f547,plain,
    ( spl6_34
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f597,plain,
    ( spl6_36
  <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f634,plain,
    ( spl6_41
  <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f694,plain,
    ( spl6_48
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f1060,plain,
    ( spl6_68
  <=> v1_funct_1(k6_partfun1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f1126,plain,
    ( spl6_72
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f1201,plain,
    ( spl6_77
  <=> u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f2982,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_13
    | ~ spl6_17
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41
    | ~ spl6_48
    | ~ spl6_68
    | ~ spl6_72
    | ~ spl6_77 ),
    inference(forward_demodulation,[],[f2981,f2715])).

fof(f2715,plain,
    ( k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_17
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41
    | ~ spl6_48
    | ~ spl6_68
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f2714,f549])).

fof(f549,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_34 ),
    inference(avatar_component_clause,[],[f547])).

fof(f2714,plain,
    ( k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_17
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41
    | ~ spl6_48
    | ~ spl6_68
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f2713,f1160])).

fof(f1160,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f1159,f712])).

fof(f712,plain,
    ( k7_tmap_1(sK0,u1_struct_0(sK0)) = k6_partfun1(u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f302,f143,f148,f153,f224])).

fof(f224,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f100,f89])).

fof(f302,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f300])).

fof(f1159,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f1158,f741])).

fof(f741,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f730,f317])).

fof(f317,plain,
    ( k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f143,f148,f153,f302,f136])).

fof(f730,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f302,f143,f148,f153,f226])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f101,f89])).

fof(f1158,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f1153,f317])).

fof(f1153,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_72 ),
    inference(unit_resulting_resolution,[],[f143,f148,f153,f1128,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f1128,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f1126])).

fof(f2713,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_17
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41
    | ~ spl6_48
    | ~ spl6_68
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f2712,f1062])).

fof(f1062,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f1060])).

fof(f2712,plain,
    ( ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_17
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41
    | ~ spl6_48
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f2709,f1163])).

fof(f1163,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f1162,f712])).

fof(f1162,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f1161,f741])).

fof(f1161,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f1152,f317])).

fof(f1152,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_72 ),
    inference(unit_resulting_resolution,[],[f143,f148,f153,f1128,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f2709,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41
    | ~ spl6_48 ),
    inference(resolution,[],[f847,f696])).

fof(f696,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f694])).

fof(f847,plain,
    ( ! [X6,X7,X5] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5)
        | ~ v1_funct_2(X5,X6,X7)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | k9_tmap_1(sK0,sK1) = X5
        | v1_xboole_0(X7) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f846,f143])).

fof(f846,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_2(X5,X6,X7)
        | ~ v1_funct_1(X5)
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5)
        | k9_tmap_1(sK0,sK1) = X5
        | v1_xboole_0(X7)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f845,f148])).

fof(f845,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_2(X5,X6,X7)
        | ~ v1_funct_1(X5)
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5)
        | k9_tmap_1(sK0,sK1) = X5
        | v1_xboole_0(X7)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_6
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f844,f153])).

fof(f844,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_2(X5,X6,X7)
        | ~ v1_funct_1(X5)
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5)
        | k9_tmap_1(sK0,sK1) = X5
        | v1_xboole_0(X7)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_6
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f843,f168])).

fof(f843,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_2(X5,X6,X7)
        | ~ v1_funct_1(X5)
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5)
        | k9_tmap_1(sK0,sK1) = X5
        | v1_xboole_0(X7)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f842,f549])).

fof(f842,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_2(X5,X6,X7)
        | ~ v1_funct_1(X5)
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5)
        | k9_tmap_1(sK0,sK1) = X5
        | v1_xboole_0(X7)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_pre_topc(sK1,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_36
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f838,f599])).

fof(f599,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f597])).

fof(f838,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_2(X5,X6,X7)
        | ~ v1_funct_1(X5)
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5)
        | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
        | k9_tmap_1(sK0,sK1) = X5
        | v1_xboole_0(X7)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_pre_topc(sK1,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_41 ),
    inference(resolution,[],[f259,f636])).

fof(f636,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f634])).

fof(f259,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k9_tmap_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X6,X2,X3)
      | ~ v1_funct_1(X6)
      | ~ r1_funct_2(X0,X1,X2,X3,k9_tmap_1(X4,X5),X6)
      | ~ v1_funct_2(k9_tmap_1(X4,X5),X0,X1)
      | k9_tmap_1(X4,X5) = X6
      | v1_xboole_0(X3)
      | v1_xboole_0(X1)
      | ~ m1_pre_topc(X5,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f124,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(f124,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | X4 = X5
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f2981,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | spl6_13
    | ~ spl6_77 ),
    inference(forward_demodulation,[],[f268,f1203])).

fof(f1203,plain,
    ( u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0)
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f1201])).

fof(f268,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f266])).

fof(f2979,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_7
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_64
    | spl6_116 ),
    inference(avatar_contradiction_clause,[],[f2978])).

fof(f2978,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_7
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_64
    | spl6_116 ),
    inference(subsumption_resolution,[],[f2977,f163])).

fof(f2977,plain,
    ( v2_struct_0(sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_64
    | spl6_116 ),
    inference(subsumption_resolution,[],[f2976,f173])).

fof(f2976,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_64
    | spl6_116 ),
    inference(subsumption_resolution,[],[f2973,f1915])).

fof(f2973,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_32
    | spl6_116 ),
    inference(resolution,[],[f2970,f540])).

fof(f540,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f539,f463])).

fof(f539,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f538,f143])).

fof(f538,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f537,f148])).

fof(f537,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f536,f153])).

fof(f536,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f520,f456])).

fof(f520,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1))
        | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_32 ),
    inference(superposition,[],[f105,f510])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2970,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k8_tmap_1(sK0,sK1))
    | spl6_116 ),
    inference(avatar_component_clause,[],[f2968])).

fof(f2968,plain,
    ( spl6_116
  <=> v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

fof(f2971,plain,
    ( ~ spl6_116
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_14
    | ~ spl6_17
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41
    | ~ spl6_48
    | ~ spl6_68
    | ~ spl6_72 ),
    inference(avatar_split_clause,[],[f2966,f1126,f1060,f694,f634,f597,f547,f300,f270,f166,f151,f146,f141,f2968])).

fof(f270,plain,
    ( spl6_14
  <=> v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f2966,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k8_tmap_1(sK0,sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_14
    | ~ spl6_17
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41
    | ~ spl6_48
    | ~ spl6_68
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f272,f2715])).

fof(f272,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f270])).

fof(f2963,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_64
    | spl6_115 ),
    inference(avatar_contradiction_clause,[],[f2962])).

fof(f2962,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_64
    | spl6_115 ),
    inference(subsumption_resolution,[],[f2961,f163])).

fof(f2961,plain,
    ( v2_struct_0(sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_64
    | spl6_115 ),
    inference(subsumption_resolution,[],[f2960,f173])).

fof(f2960,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_16
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_64
    | spl6_115 ),
    inference(subsumption_resolution,[],[f2957,f1915])).

fof(f2957,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_32
    | spl6_115 ),
    inference(resolution,[],[f2954,f529])).

fof(f529,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f528,f463])).

fof(f528,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f527,f476])).

fof(f527,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f526,f143])).

fof(f526,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f525,f148])).

fof(f525,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f524,f153])).

fof(f524,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f518,f456])).

fof(f518,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_32 ),
    inference(superposition,[],[f106,f510])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2954,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | spl6_115 ),
    inference(avatar_component_clause,[],[f2952])).

fof(f2952,plain,
    ( spl6_115
  <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).

fof(f2955,plain,
    ( ~ spl6_115
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_15
    | ~ spl6_17
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41
    | ~ spl6_48
    | ~ spl6_68
    | ~ spl6_72
    | ~ spl6_77 ),
    inference(avatar_split_clause,[],[f2949,f1201,f1126,f1060,f694,f634,f597,f547,f300,f274,f166,f151,f146,f141,f2952])).

fof(f274,plain,
    ( spl6_15
  <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f2949,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_15
    | ~ spl6_17
    | spl6_34
    | ~ spl6_36
    | ~ spl6_41
    | ~ spl6_48
    | ~ spl6_68
    | ~ spl6_72
    | ~ spl6_77 ),
    inference(forward_demodulation,[],[f2948,f2715])).

fof(f2948,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | spl6_15
    | ~ spl6_77 ),
    inference(forward_demodulation,[],[f276,f1203])).

fof(f276,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f274])).

fof(f2931,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_12
    | ~ spl6_24
    | ~ spl6_58 ),
    inference(avatar_contradiction_clause,[],[f2930])).

fof(f2930,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_12
    | ~ spl6_24
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f2884,f264])).

fof(f264,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl6_12
  <=> v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f2884,plain,
    ( v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_24
    | ~ spl6_58 ),
    inference(unit_resulting_resolution,[],[f352,f143,f148,f153,f168,f919,f824])).

fof(f824,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(k8_tmap_1(X1,X2))
      | v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0))
      | ~ l1_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f823,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f823,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
      | v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0))
      | ~ l1_struct_0(k8_tmap_1(X1,X2))
      | ~ m1_pre_topc(X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f822,f86])).

fof(f86,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f822,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
      | v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0))
      | ~ l1_struct_0(k8_tmap_1(X1,X2))
      | ~ l1_struct_0(X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f817])).

fof(f817,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
      | v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0))
      | ~ l1_struct_0(k8_tmap_1(X1,X2))
      | ~ l1_struct_0(X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f249,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f249,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ l1_struct_0(X0)
      | ~ v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X3),u1_struct_0(X4))
      | v1_funct_1(k2_tmap_1(X3,X4,k9_tmap_1(X1,X2),X0))
      | ~ l1_struct_0(X4)
      | ~ l1_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f121,f114])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f919,plain,
    ( l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f917])).

fof(f917,plain,
    ( spl6_58
  <=> l1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f1204,plain,
    ( spl6_77
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f476,f454,f166,f151,f146,f141,f1201])).

fof(f1129,plain,
    ( spl6_72
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f305,f300,f151,f1126])).

fof(f305,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f153,f302,f89])).

fof(f1063,plain,
    ( spl6_68
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_67 ),
    inference(avatar_split_clause,[],[f1058,f1054,f454,f151,f146,f141,f1060])).

fof(f1054,plain,
    ( spl6_67
  <=> v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f1058,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_67 ),
    inference(forward_demodulation,[],[f1056,f463])).

fof(f1056,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f1054])).

fof(f1057,plain,
    ( spl6_67
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f466,f454,f151,f146,f141,f1054])).

fof(f466,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f143,f148,f153,f456,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1042,plain,
    ( spl6_64
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f441,f350,f295,f176,f1039])).

fof(f176,plain,
    ( spl6_8
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f441,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f297,f178,f352,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f178,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f920,plain,
    ( spl6_58
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f427,f360,f917])).

fof(f360,plain,
    ( spl6_26
  <=> l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f427,plain,
    ( l1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f362,f86])).

fof(f362,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f360])).

fof(f697,plain,
    ( spl6_48
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f692,f687,f454,f166,f151,f146,f141,f694])).

fof(f687,plain,
    ( spl6_47
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f692,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_47 ),
    inference(forward_demodulation,[],[f691,f476])).

fof(f691,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_47 ),
    inference(forward_demodulation,[],[f689,f463])).

fof(f689,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f687])).

fof(f690,plain,
    ( spl6_47
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f254,f166,f151,f146,f141,f687])).

fof(f254,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f251,f215])).

fof(f251,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f143,f148,f153,f168,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f138,f114])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f137,f115])).

fof(f137,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f133,f116])).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f129,f89])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2)))
                    & u1_struct_0(X1) = sK5(X0,X1,X2)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f71,f72])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2)))
        & u1_struct_0(X1) = sK5(X0,X1,X2)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).

fof(f637,plain,
    ( spl6_41
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f632,f628,f454,f166,f151,f146,f141,f634])).

fof(f628,plain,
    ( spl6_40
  <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f632,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f630,f476])).

fof(f630,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f628])).

fof(f631,plain,
    ( spl6_40
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f236,f166,f151,f146,f141,f628])).

fof(f236,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f143,f148,f153,f168,f116])).

fof(f600,plain,
    ( spl6_36
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f595,f591,f454,f166,f151,f146,f141,f597])).

fof(f591,plain,
    ( spl6_35
  <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f595,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f593,f476])).

fof(f593,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f591])).

fof(f594,plain,
    ( spl6_35
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f234,f166,f151,f146,f141,f591])).

fof(f234,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f143,f148,f153,f168,f115])).

fof(f550,plain,
    ( ~ spl6_34
    | spl6_1
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f200,f184,f141,f547])).

fof(f184,plain,
    ( spl6_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f200,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f143,f186,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f186,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f184])).

fof(f511,plain,
    ( spl6_32
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f215,f166,f151,f146,f141,f508])).

fof(f457,plain,
    ( spl6_30
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f192,f166,f151,f454])).

fof(f192,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f153,f168,f89])).

fof(f363,plain,
    ( spl6_26
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f208,f166,f151,f146,f141,f360])).

fof(f208,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f143,f148,f153,f168,f113])).

fof(f353,plain,
    ( spl6_24
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f290,f245,f350])).

fof(f245,plain,
    ( spl6_11
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f290,plain,
    ( l1_struct_0(sK2)
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f247,f86])).

fof(f247,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f245])).

fof(f303,plain,
    ( spl6_17
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f181,f151,f300])).

fof(f181,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f153,f87])).

fof(f87,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f298,plain,
    ( spl6_16
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f255,f228,f295])).

fof(f228,plain,
    ( spl6_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f255,plain,
    ( l1_struct_0(sK1)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f230,f86])).

fof(f230,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f228])).

fof(f277,plain,
    ( ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f83,f274,f270,f266,f262])).

fof(f83,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) )
    & r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f61,f60,f59])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
                & r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X2,k8_tmap_1(sK0,X1))
                | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1)))
                | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1)))))
              | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X2,k8_tmap_1(sK0,X1))
              | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1)))
              | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2)) )
            & r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
            | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X2,k8_tmap_1(sK0,sK1))
            | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1)))
            | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2)) )
          & r1_tsep_1(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X2] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
          | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X2,k8_tmap_1(sK0,sK1))
          | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1)))
          | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2)) )
        & r1_tsep_1(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) )
      & r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_tsep_1(X1,X2)
                 => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tsep_1(X1,X2)
               => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_tmap_1)).

fof(f248,plain,
    ( spl6_11
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f189,f171,f151,f245])).

fof(f189,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f173,f153,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f231,plain,
    ( spl6_10
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f188,f166,f151,f228])).

fof(f188,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f168,f153,f88])).

fof(f187,plain,
    ( spl6_9
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f180,f151,f184])).

fof(f180,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f153,f86])).

fof(f179,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f82,f176])).

fof(f82,plain,(
    r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f174,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f81,f171])).

fof(f81,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f169,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f79,f166])).

fof(f79,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f164,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f80,f161])).

fof(f80,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f154,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f77,f151])).

fof(f77,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f149,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f76,f146])).

fof(f76,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f144,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f75,f141])).

fof(f75,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (21688)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.48  % (21688)Refutation not found, incomplete strategy% (21688)------------------------------
% 0.21/0.48  % (21688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21696)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (21688)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21688)Memory used [KB]: 10746
% 0.21/0.48  % (21688)Time elapsed: 0.060 s
% 0.21/0.48  % (21688)------------------------------
% 0.21/0.48  % (21688)------------------------------
% 0.21/0.51  % (21690)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (21689)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (21698)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (21695)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (21705)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (21691)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (21687)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (21702)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (21706)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (21686)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (21682)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (21704)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (21683)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (21703)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (21697)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (21685)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (21701)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (21684)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (21699)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (21694)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.55  % (21700)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (21693)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (21692)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.56  % (21707)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.21/0.65  % (21691)Refutation not found, incomplete strategy% (21691)------------------------------
% 2.21/0.65  % (21691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (21691)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.65  
% 2.21/0.65  % (21691)Memory used [KB]: 6140
% 2.21/0.65  % (21691)Time elapsed: 0.229 s
% 2.21/0.65  % (21691)------------------------------
% 2.21/0.65  % (21691)------------------------------
% 2.21/0.66  % (21705)Refutation found. Thanks to Tanya!
% 2.21/0.66  % SZS status Theorem for theBenchmark
% 2.21/0.66  % SZS output start Proof for theBenchmark
% 2.21/0.66  fof(f2996,plain,(
% 2.21/0.66    $false),
% 2.21/0.66    inference(avatar_sat_refutation,[],[f144,f149,f154,f164,f169,f174,f179,f187,f231,f248,f277,f298,f303,f353,f363,f457,f511,f550,f594,f600,f631,f637,f690,f697,f920,f1042,f1057,f1063,f1129,f1204,f2931,f2955,f2963,f2971,f2979,f2987,f2995])).
% 2.21/0.66  fof(f2995,plain,(
% 2.21/0.66    spl6_1 | ~spl6_2 | ~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_16 | ~spl6_24 | ~spl6_30 | ~spl6_32 | ~spl6_64 | spl6_117),
% 2.21/0.66    inference(avatar_contradiction_clause,[],[f2994])).
% 2.21/0.66  fof(f2994,plain,(
% 2.21/0.66    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_16 | ~spl6_24 | ~spl6_30 | ~spl6_32 | ~spl6_64 | spl6_117)),
% 2.21/0.66    inference(subsumption_resolution,[],[f2993,f163])).
% 2.21/0.66  fof(f163,plain,(
% 2.21/0.66    ~v2_struct_0(sK2) | spl6_5),
% 2.21/0.66    inference(avatar_component_clause,[],[f161])).
% 2.21/0.66  fof(f161,plain,(
% 2.21/0.66    spl6_5 <=> v2_struct_0(sK2)),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.21/0.66  fof(f2993,plain,(
% 2.21/0.66    v2_struct_0(sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_16 | ~spl6_24 | ~spl6_30 | ~spl6_32 | ~spl6_64 | spl6_117)),
% 2.21/0.66    inference(subsumption_resolution,[],[f2992,f173])).
% 2.21/0.66  fof(f173,plain,(
% 2.21/0.66    m1_pre_topc(sK2,sK0) | ~spl6_7),
% 2.21/0.66    inference(avatar_component_clause,[],[f171])).
% 2.21/0.66  fof(f171,plain,(
% 2.21/0.66    spl6_7 <=> m1_pre_topc(sK2,sK0)),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.21/0.66  fof(f2992,plain,(
% 2.21/0.66    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_16 | ~spl6_24 | ~spl6_30 | ~spl6_32 | ~spl6_64 | spl6_117)),
% 2.21/0.66    inference(subsumption_resolution,[],[f2989,f1915])).
% 2.21/0.66  fof(f1915,plain,(
% 2.21/0.66    r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | (~spl6_16 | ~spl6_24 | ~spl6_64)),
% 2.21/0.66    inference(unit_resulting_resolution,[],[f352,f297,f1041,f84])).
% 2.21/0.66  fof(f84,plain,(
% 2.21/0.66    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.21/0.66    inference(cnf_transformation,[],[f63])).
% 2.21/0.66  fof(f63,plain,(
% 2.21/0.66    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.21/0.66    inference(nnf_transformation,[],[f25])).
% 2.21/0.66  fof(f25,plain,(
% 2.21/0.66    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.21/0.66    inference(ennf_transformation,[],[f9])).
% 2.21/0.66  fof(f9,axiom,(
% 2.21/0.66    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 2.21/0.66  fof(f1041,plain,(
% 2.21/0.66    r1_tsep_1(sK2,sK1) | ~spl6_64),
% 2.21/0.66    inference(avatar_component_clause,[],[f1039])).
% 2.21/0.66  fof(f1039,plain,(
% 2.21/0.66    spl6_64 <=> r1_tsep_1(sK2,sK1)),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 2.21/0.66  fof(f297,plain,(
% 2.21/0.66    l1_struct_0(sK1) | ~spl6_16),
% 2.21/0.66    inference(avatar_component_clause,[],[f295])).
% 2.21/0.66  fof(f295,plain,(
% 2.21/0.66    spl6_16 <=> l1_struct_0(sK1)),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.21/0.66  fof(f352,plain,(
% 2.21/0.66    l1_struct_0(sK2) | ~spl6_24),
% 2.21/0.66    inference(avatar_component_clause,[],[f350])).
% 2.21/0.66  fof(f350,plain,(
% 2.21/0.66    spl6_24 <=> l1_struct_0(sK2)),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 2.21/0.66  fof(f2989,plain,(
% 2.21/0.66    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30 | ~spl6_32 | spl6_117)),
% 2.21/0.66    inference(resolution,[],[f2986,f535])).
% 2.21/0.66  fof(f535,plain,(
% 2.21/0.66    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X1),u1_struct_0(X1),u1_struct_0(sK0)) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30 | ~spl6_32)),
% 2.21/0.66    inference(forward_demodulation,[],[f534,f463])).
% 2.21/0.66  fof(f463,plain,(
% 2.21/0.66    k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30)),
% 2.21/0.66    inference(unit_resulting_resolution,[],[f143,f148,f153,f456,f100])).
% 2.21/0.66  fof(f100,plain,(
% 2.21/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.66    inference(cnf_transformation,[],[f38])).
% 2.21/0.66  fof(f38,plain,(
% 2.21/0.66    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.66    inference(flattening,[],[f37])).
% 2.21/0.66  fof(f37,plain,(
% 2.21/0.66    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.66    inference(ennf_transformation,[],[f6])).
% 2.21/0.66  fof(f6,axiom,(
% 2.21/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).
% 2.21/0.66  fof(f456,plain,(
% 2.21/0.66    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_30),
% 2.21/0.66    inference(avatar_component_clause,[],[f454])).
% 2.21/0.66  fof(f454,plain,(
% 2.21/0.66    spl6_30 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 2.21/0.66  fof(f153,plain,(
% 2.21/0.66    l1_pre_topc(sK0) | ~spl6_3),
% 2.21/0.66    inference(avatar_component_clause,[],[f151])).
% 2.21/0.66  fof(f151,plain,(
% 2.21/0.66    spl6_3 <=> l1_pre_topc(sK0)),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.21/0.66  fof(f148,plain,(
% 2.21/0.66    v2_pre_topc(sK0) | ~spl6_2),
% 2.21/0.66    inference(avatar_component_clause,[],[f146])).
% 2.21/0.66  fof(f146,plain,(
% 2.21/0.66    spl6_2 <=> v2_pre_topc(sK0)),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.21/0.66  fof(f143,plain,(
% 2.21/0.66    ~v2_struct_0(sK0) | spl6_1),
% 2.21/0.66    inference(avatar_component_clause,[],[f141])).
% 2.21/0.66  fof(f141,plain,(
% 2.21/0.66    spl6_1 <=> v2_struct_0(sK0)),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.21/0.66  fof(f534,plain,(
% 2.21/0.66    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(sK0)) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30 | ~spl6_32)),
% 2.21/0.66    inference(forward_demodulation,[],[f533,f476])).
% 2.21/0.66  fof(f476,plain,(
% 2.21/0.66    u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30)),
% 2.21/0.66    inference(forward_demodulation,[],[f464,f215])).
% 2.21/0.66  fof(f215,plain,(
% 2.21/0.66    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6)),
% 2.21/0.66    inference(unit_resulting_resolution,[],[f143,f148,f153,f168,f136])).
% 2.21/0.66  fof(f136,plain,(
% 2.21/0.66    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0)) )),
% 2.21/0.66    inference(subsumption_resolution,[],[f135,f113])).
% 2.21/0.66  fof(f113,plain,(
% 2.21/0.66    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.66    inference(cnf_transformation,[],[f48])).
% 2.21/0.66  fof(f48,plain,(
% 2.21/0.66    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.66    inference(flattening,[],[f47])).
% 2.21/0.66  fof(f47,plain,(
% 2.21/0.66    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.66    inference(ennf_transformation,[],[f12])).
% 2.21/0.66  fof(f12,axiom,(
% 2.21/0.66    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 2.21/0.66  fof(f135,plain,(
% 2.21/0.66    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.66    inference(subsumption_resolution,[],[f134,f109])).
% 2.21/0.67  fof(f109,plain,(
% 2.21/0.67    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f46])).
% 2.21/0.67  fof(f46,plain,(
% 2.21/0.67    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(flattening,[],[f45])).
% 2.21/0.67  fof(f45,plain,(
% 2.21/0.67    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f14])).
% 2.21/0.67  fof(f14,axiom,(
% 2.21/0.67    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tmap_1)).
% 2.21/0.67  fof(f134,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(subsumption_resolution,[],[f132,f110])).
% 2.21/0.67  fof(f110,plain,(
% 2.21/0.67    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f46])).
% 2.21/0.67  fof(f132,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(subsumption_resolution,[],[f127,f89])).
% 2.21/0.67  fof(f89,plain,(
% 2.21/0.67    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f29])).
% 2.21/0.67  fof(f29,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.21/0.67    inference(ennf_transformation,[],[f18])).
% 2.21/0.67  fof(f18,axiom,(
% 2.21/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.21/0.67  fof(f127,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(equality_resolution,[],[f126])).
% 2.21/0.67  fof(f126,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(equality_resolution,[],[f92])).
% 2.21/0.67  fof(f92,plain,(
% 2.21/0.67    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f69])).
% 2.21/0.67  fof(f69,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK4(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f67,f68])).
% 2.21/0.67  fof(f68,plain,(
% 2.21/0.67    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK4(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.21/0.67    introduced(choice_axiom,[])).
% 2.21/0.67  fof(f67,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(rectify,[],[f66])).
% 2.21/0.67  fof(f66,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(nnf_transformation,[],[f34])).
% 2.21/0.67  fof(f34,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(flattening,[],[f33])).
% 2.21/0.67  fof(f33,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f7])).
% 2.21/0.67  fof(f7,axiom,(
% 2.21/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).
% 2.21/0.67  fof(f168,plain,(
% 2.21/0.67    m1_pre_topc(sK1,sK0) | ~spl6_6),
% 2.21/0.67    inference(avatar_component_clause,[],[f166])).
% 2.21/0.67  fof(f166,plain,(
% 2.21/0.67    spl6_6 <=> m1_pre_topc(sK1,sK0)),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.21/0.67  fof(f464,plain,(
% 2.21/0.67    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f143,f148,f153,f456,f101])).
% 2.21/0.67  fof(f101,plain,(
% 2.21/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f40])).
% 2.21/0.67  fof(f40,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(flattening,[],[f39])).
% 2.21/0.67  fof(f39,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f16])).
% 2.21/0.67  fof(f16,axiom,(
% 2.21/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 2.21/0.67  fof(f533,plain,(
% 2.21/0.67    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(subsumption_resolution,[],[f532,f143])).
% 2.21/0.67  fof(f532,plain,(
% 2.21/0.67    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(subsumption_resolution,[],[f531,f148])).
% 2.21/0.67  fof(f531,plain,(
% 2.21/0.67    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(subsumption_resolution,[],[f530,f153])).
% 2.21/0.67  fof(f530,plain,(
% 2.21/0.67    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(subsumption_resolution,[],[f519,f456])).
% 2.21/0.67  fof(f519,plain,(
% 2.21/0.67    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_32),
% 2.21/0.67    inference(superposition,[],[f104,f510])).
% 2.21/0.67  fof(f510,plain,(
% 2.21/0.67    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_32),
% 2.21/0.67    inference(avatar_component_clause,[],[f508])).
% 2.21/0.67  fof(f508,plain,(
% 2.21/0.67    spl6_32 <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 2.21/0.67  fof(f104,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f42])).
% 2.21/0.67  fof(f42,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : ((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(flattening,[],[f41])).
% 2.21/0.67  fof(f41,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : (((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | ~r1_xboole_0(u1_struct_0(X2),X1)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f17])).
% 2.21/0.67  fof(f17,axiom,(
% 2.21/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tmap_1)).
% 2.21/0.67  fof(f2986,plain,(
% 2.21/0.67    ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | spl6_117),
% 2.21/0.67    inference(avatar_component_clause,[],[f2984])).
% 2.21/0.67  fof(f2984,plain,(
% 2.21/0.67    spl6_117 <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(sK0))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).
% 2.21/0.67  fof(f2987,plain,(
% 2.21/0.67    ~spl6_117 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_13 | ~spl6_17 | spl6_34 | ~spl6_36 | ~spl6_41 | ~spl6_48 | ~spl6_68 | ~spl6_72 | ~spl6_77),
% 2.21/0.67    inference(avatar_split_clause,[],[f2982,f1201,f1126,f1060,f694,f634,f597,f547,f300,f266,f166,f151,f146,f141,f2984])).
% 2.21/0.67  fof(f266,plain,(
% 2.21/0.67    spl6_13 <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.21/0.67  fof(f300,plain,(
% 2.21/0.67    spl6_17 <=> m1_pre_topc(sK0,sK0)),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 2.21/0.67  fof(f547,plain,(
% 2.21/0.67    spl6_34 <=> v1_xboole_0(u1_struct_0(sK0))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 2.21/0.67  fof(f597,plain,(
% 2.21/0.67    spl6_36 <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 2.21/0.67  fof(f634,plain,(
% 2.21/0.67    spl6_41 <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 2.21/0.67  fof(f694,plain,(
% 2.21/0.67    spl6_48 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 2.21/0.67  fof(f1060,plain,(
% 2.21/0.67    spl6_68 <=> v1_funct_1(k6_partfun1(u1_struct_0(sK0)))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 2.21/0.67  fof(f1126,plain,(
% 2.21/0.67    spl6_72 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).
% 2.21/0.67  fof(f1201,plain,(
% 2.21/0.67    spl6_77 <=> u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0)),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 2.21/0.67  fof(f2982,plain,(
% 2.21/0.67    ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_13 | ~spl6_17 | spl6_34 | ~spl6_36 | ~spl6_41 | ~spl6_48 | ~spl6_68 | ~spl6_72 | ~spl6_77)),
% 2.21/0.67    inference(forward_demodulation,[],[f2981,f2715])).
% 2.21/0.67  fof(f2715,plain,(
% 2.21/0.67    k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_17 | spl6_34 | ~spl6_36 | ~spl6_41 | ~spl6_48 | ~spl6_68 | ~spl6_72)),
% 2.21/0.67    inference(subsumption_resolution,[],[f2714,f549])).
% 2.21/0.67  fof(f549,plain,(
% 2.21/0.67    ~v1_xboole_0(u1_struct_0(sK0)) | spl6_34),
% 2.21/0.67    inference(avatar_component_clause,[],[f547])).
% 2.21/0.67  fof(f2714,plain,(
% 2.21/0.67    k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_17 | spl6_34 | ~spl6_36 | ~spl6_41 | ~spl6_48 | ~spl6_68 | ~spl6_72)),
% 2.21/0.67    inference(subsumption_resolution,[],[f2713,f1160])).
% 2.21/0.67  fof(f1160,plain,(
% 2.21/0.67    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_72)),
% 2.21/0.67    inference(forward_demodulation,[],[f1159,f712])).
% 2.21/0.67  fof(f712,plain,(
% 2.21/0.67    k7_tmap_1(sK0,u1_struct_0(sK0)) = k6_partfun1(u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f302,f143,f148,f153,f224])).
% 2.21/0.67  fof(f224,plain,(
% 2.21/0.67    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0)) )),
% 2.21/0.67    inference(duplicate_literal_removal,[],[f223])).
% 2.21/0.67  fof(f223,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(resolution,[],[f100,f89])).
% 2.21/0.67  fof(f302,plain,(
% 2.21/0.67    m1_pre_topc(sK0,sK0) | ~spl6_17),
% 2.21/0.67    inference(avatar_component_clause,[],[f300])).
% 2.21/0.67  fof(f1159,plain,(
% 2.21/0.67    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_72)),
% 2.21/0.67    inference(forward_demodulation,[],[f1158,f741])).
% 2.21/0.67  fof(f741,plain,(
% 2.21/0.67    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17)),
% 2.21/0.67    inference(forward_demodulation,[],[f730,f317])).
% 2.21/0.67  fof(f317,plain,(
% 2.21/0.67    k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f143,f148,f153,f302,f136])).
% 2.21/0.67  fof(f730,plain,(
% 2.21/0.67    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f302,f143,f148,f153,f226])).
% 2.21/0.67  fof(f226,plain,(
% 2.21/0.67    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0)) )),
% 2.21/0.67    inference(duplicate_literal_removal,[],[f225])).
% 2.21/0.67  fof(f225,plain,(
% 2.21/0.67    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(resolution,[],[f101,f89])).
% 2.21/0.67  fof(f1158,plain,(
% 2.21/0.67    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_72)),
% 2.21/0.67    inference(forward_demodulation,[],[f1153,f317])).
% 2.21/0.67  fof(f1153,plain,(
% 2.21/0.67    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_72)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f143,f148,f153,f1128,f119])).
% 2.21/0.67  fof(f119,plain,(
% 2.21/0.67    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f52])).
% 2.21/0.67  fof(f52,plain,(
% 2.21/0.67    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(flattening,[],[f51])).
% 2.21/0.67  fof(f51,plain,(
% 2.21/0.67    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f11])).
% 2.21/0.67  fof(f11,axiom,(
% 2.21/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 2.21/0.67  fof(f1128,plain,(
% 2.21/0.67    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_72),
% 2.21/0.67    inference(avatar_component_clause,[],[f1126])).
% 2.21/0.67  fof(f2713,plain,(
% 2.21/0.67    ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_17 | spl6_34 | ~spl6_36 | ~spl6_41 | ~spl6_48 | ~spl6_68 | ~spl6_72)),
% 2.21/0.67    inference(subsumption_resolution,[],[f2712,f1062])).
% 2.21/0.67  fof(f1062,plain,(
% 2.21/0.67    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~spl6_68),
% 2.21/0.67    inference(avatar_component_clause,[],[f1060])).
% 2.21/0.67  fof(f2712,plain,(
% 2.21/0.67    ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_17 | spl6_34 | ~spl6_36 | ~spl6_41 | ~spl6_48 | ~spl6_72)),
% 2.21/0.67    inference(subsumption_resolution,[],[f2709,f1163])).
% 2.21/0.67  fof(f1163,plain,(
% 2.21/0.67    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_72)),
% 2.21/0.67    inference(forward_demodulation,[],[f1162,f712])).
% 2.21/0.67  fof(f1162,plain,(
% 2.21/0.67    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_72)),
% 2.21/0.67    inference(forward_demodulation,[],[f1161,f741])).
% 2.21/0.67  fof(f1161,plain,(
% 2.21/0.67    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_72)),
% 2.21/0.67    inference(forward_demodulation,[],[f1152,f317])).
% 2.21/0.67  fof(f1152,plain,(
% 2.21/0.67    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_72)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f143,f148,f153,f1128,f118])).
% 2.21/0.67  fof(f118,plain,(
% 2.21/0.67    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f52])).
% 2.21/0.67  fof(f2709,plain,(
% 2.21/0.67    ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_34 | ~spl6_36 | ~spl6_41 | ~spl6_48)),
% 2.21/0.67    inference(resolution,[],[f847,f696])).
% 2.21/0.67  fof(f696,plain,(
% 2.21/0.67    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0))) | ~spl6_48),
% 2.21/0.67    inference(avatar_component_clause,[],[f694])).
% 2.21/0.67  fof(f847,plain,(
% 2.21/0.67    ( ! [X6,X7,X5] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5) | ~v1_funct_2(X5,X6,X7) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k9_tmap_1(sK0,sK1) = X5 | v1_xboole_0(X7)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_34 | ~spl6_36 | ~spl6_41)),
% 2.21/0.67    inference(subsumption_resolution,[],[f846,f143])).
% 2.21/0.67  fof(f846,plain,(
% 2.21/0.67    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(X5,X6,X7) | ~v1_funct_1(X5) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5) | k9_tmap_1(sK0,sK1) = X5 | v1_xboole_0(X7) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_34 | ~spl6_36 | ~spl6_41)),
% 2.21/0.67    inference(subsumption_resolution,[],[f845,f148])).
% 2.21/0.67  fof(f845,plain,(
% 2.21/0.67    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(X5,X6,X7) | ~v1_funct_1(X5) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5) | k9_tmap_1(sK0,sK1) = X5 | v1_xboole_0(X7) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_6 | spl6_34 | ~spl6_36 | ~spl6_41)),
% 2.21/0.67    inference(subsumption_resolution,[],[f844,f153])).
% 2.21/0.67  fof(f844,plain,(
% 2.21/0.67    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(X5,X6,X7) | ~v1_funct_1(X5) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5) | k9_tmap_1(sK0,sK1) = X5 | v1_xboole_0(X7) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_6 | spl6_34 | ~spl6_36 | ~spl6_41)),
% 2.21/0.67    inference(subsumption_resolution,[],[f843,f168])).
% 2.21/0.67  fof(f843,plain,(
% 2.21/0.67    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(X5,X6,X7) | ~v1_funct_1(X5) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5) | k9_tmap_1(sK0,sK1) = X5 | v1_xboole_0(X7) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_34 | ~spl6_36 | ~spl6_41)),
% 2.21/0.67    inference(subsumption_resolution,[],[f842,f549])).
% 2.21/0.67  fof(f842,plain,(
% 2.21/0.67    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(X5,X6,X7) | ~v1_funct_1(X5) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5) | k9_tmap_1(sK0,sK1) = X5 | v1_xboole_0(X7) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_36 | ~spl6_41)),
% 2.21/0.67    inference(subsumption_resolution,[],[f838,f599])).
% 2.21/0.67  fof(f599,plain,(
% 2.21/0.67    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl6_36),
% 2.21/0.67    inference(avatar_component_clause,[],[f597])).
% 2.21/0.67  fof(f838,plain,(
% 2.21/0.67    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(X5,X6,X7) | ~v1_funct_1(X5) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7,k9_tmap_1(sK0,sK1),X5) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | k9_tmap_1(sK0,sK1) = X5 | v1_xboole_0(X7) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_41),
% 2.21/0.67    inference(resolution,[],[f259,f636])).
% 2.21/0.67  fof(f636,plain,(
% 2.21/0.67    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl6_41),
% 2.21/0.67    inference(avatar_component_clause,[],[f634])).
% 2.21/0.67  fof(f259,plain,(
% 2.21/0.67    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k9_tmap_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X6,X2,X3) | ~v1_funct_1(X6) | ~r1_funct_2(X0,X1,X2,X3,k9_tmap_1(X4,X5),X6) | ~v1_funct_2(k9_tmap_1(X4,X5),X0,X1) | k9_tmap_1(X4,X5) = X6 | v1_xboole_0(X3) | v1_xboole_0(X1) | ~m1_pre_topc(X5,X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.21/0.67    inference(resolution,[],[f124,f114])).
% 2.21/0.67  fof(f114,plain,(
% 2.21/0.67    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f50])).
% 2.21/0.67  fof(f50,plain,(
% 2.21/0.67    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(flattening,[],[f49])).
% 2.21/0.67  fof(f49,plain,(
% 2.21/0.67    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f13])).
% 2.21/0.67  fof(f13,axiom,(
% 2.21/0.67    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).
% 2.21/0.67  fof(f124,plain,(
% 2.21/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | X4 = X5 | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f74])).
% 2.21/0.67  fof(f74,plain,(
% 2.21/0.67    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.21/0.67    inference(nnf_transformation,[],[f58])).
% 2.21/0.67  fof(f58,plain,(
% 2.21/0.67    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.21/0.67    inference(flattening,[],[f57])).
% 2.21/0.67  fof(f57,plain,(
% 2.21/0.67    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.21/0.67    inference(ennf_transformation,[],[f5])).
% 2.21/0.67  fof(f5,axiom,(
% 2.21/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 2.21/0.67  fof(f2981,plain,(
% 2.21/0.67    ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | (spl6_13 | ~spl6_77)),
% 2.21/0.67    inference(forward_demodulation,[],[f268,f1203])).
% 2.21/0.67  fof(f1203,plain,(
% 2.21/0.67    u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0) | ~spl6_77),
% 2.21/0.67    inference(avatar_component_clause,[],[f1201])).
% 2.21/0.67  fof(f268,plain,(
% 2.21/0.67    ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))) | spl6_13),
% 2.21/0.67    inference(avatar_component_clause,[],[f266])).
% 2.21/0.67  fof(f2979,plain,(
% 2.21/0.67    spl6_1 | ~spl6_2 | ~spl6_3 | spl6_5 | ~spl6_7 | ~spl6_16 | ~spl6_24 | ~spl6_30 | ~spl6_32 | ~spl6_64 | spl6_116),
% 2.21/0.67    inference(avatar_contradiction_clause,[],[f2978])).
% 2.21/0.67  fof(f2978,plain,(
% 2.21/0.67    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_5 | ~spl6_7 | ~spl6_16 | ~spl6_24 | ~spl6_30 | ~spl6_32 | ~spl6_64 | spl6_116)),
% 2.21/0.67    inference(subsumption_resolution,[],[f2977,f163])).
% 2.21/0.67  fof(f2977,plain,(
% 2.21/0.67    v2_struct_0(sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_16 | ~spl6_24 | ~spl6_30 | ~spl6_32 | ~spl6_64 | spl6_116)),
% 2.21/0.67    inference(subsumption_resolution,[],[f2976,f173])).
% 2.21/0.67  fof(f2976,plain,(
% 2.21/0.67    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_16 | ~spl6_24 | ~spl6_30 | ~spl6_32 | ~spl6_64 | spl6_116)),
% 2.21/0.67    inference(subsumption_resolution,[],[f2973,f1915])).
% 2.21/0.67  fof(f2973,plain,(
% 2.21/0.67    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30 | ~spl6_32 | spl6_116)),
% 2.21/0.67    inference(resolution,[],[f2970,f540])).
% 2.21/0.67  fof(f540,plain,(
% 2.21/0.67    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(forward_demodulation,[],[f539,f463])).
% 2.21/0.67  fof(f539,plain,(
% 2.21/0.67    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(subsumption_resolution,[],[f538,f143])).
% 2.21/0.67  fof(f538,plain,(
% 2.21/0.67    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(subsumption_resolution,[],[f537,f148])).
% 2.21/0.67  fof(f537,plain,(
% 2.21/0.67    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(subsumption_resolution,[],[f536,f153])).
% 2.21/0.67  fof(f536,plain,(
% 2.21/0.67    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(subsumption_resolution,[],[f520,f456])).
% 2.21/0.67  fof(f520,plain,(
% 2.21/0.67    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X2),X2,k8_tmap_1(sK0,sK1)) | ~r1_xboole_0(u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_32),
% 2.21/0.67    inference(superposition,[],[f105,f510])).
% 2.21/0.67  fof(f105,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f42])).
% 2.21/0.67  fof(f2970,plain,(
% 2.21/0.67    ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k8_tmap_1(sK0,sK1)) | spl6_116),
% 2.21/0.67    inference(avatar_component_clause,[],[f2968])).
% 2.21/0.67  fof(f2968,plain,(
% 2.21/0.67    spl6_116 <=> v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k8_tmap_1(sK0,sK1))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).
% 2.21/0.67  fof(f2971,plain,(
% 2.21/0.67    ~spl6_116 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_14 | ~spl6_17 | spl6_34 | ~spl6_36 | ~spl6_41 | ~spl6_48 | ~spl6_68 | ~spl6_72),
% 2.21/0.67    inference(avatar_split_clause,[],[f2966,f1126,f1060,f694,f634,f597,f547,f300,f270,f166,f151,f146,f141,f2968])).
% 2.21/0.67  fof(f270,plain,(
% 2.21/0.67    spl6_14 <=> v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.21/0.67  fof(f2966,plain,(
% 2.21/0.67    ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK2,k8_tmap_1(sK0,sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_14 | ~spl6_17 | spl6_34 | ~spl6_36 | ~spl6_41 | ~spl6_48 | ~spl6_68 | ~spl6_72)),
% 2.21/0.67    inference(forward_demodulation,[],[f272,f2715])).
% 2.21/0.67  fof(f272,plain,(
% 2.21/0.67    ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1)) | spl6_14),
% 2.21/0.67    inference(avatar_component_clause,[],[f270])).
% 2.21/0.67  fof(f2963,plain,(
% 2.21/0.67    spl6_1 | ~spl6_2 | ~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_16 | ~spl6_24 | ~spl6_30 | ~spl6_32 | ~spl6_64 | spl6_115),
% 2.21/0.67    inference(avatar_contradiction_clause,[],[f2962])).
% 2.21/0.67  fof(f2962,plain,(
% 2.21/0.67    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_16 | ~spl6_24 | ~spl6_30 | ~spl6_32 | ~spl6_64 | spl6_115)),
% 2.21/0.67    inference(subsumption_resolution,[],[f2961,f163])).
% 2.21/0.67  fof(f2961,plain,(
% 2.21/0.67    v2_struct_0(sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_16 | ~spl6_24 | ~spl6_30 | ~spl6_32 | ~spl6_64 | spl6_115)),
% 2.21/0.67    inference(subsumption_resolution,[],[f2960,f173])).
% 2.21/0.67  fof(f2960,plain,(
% 2.21/0.67    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_16 | ~spl6_24 | ~spl6_30 | ~spl6_32 | ~spl6_64 | spl6_115)),
% 2.21/0.67    inference(subsumption_resolution,[],[f2957,f1915])).
% 2.21/0.67  fof(f2957,plain,(
% 2.21/0.67    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30 | ~spl6_32 | spl6_115)),
% 2.21/0.67    inference(resolution,[],[f2954,f529])).
% 2.21/0.67  fof(f529,plain,(
% 2.21/0.67    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(forward_demodulation,[],[f528,f463])).
% 2.21/0.67  fof(f528,plain,(
% 2.21/0.67    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(forward_demodulation,[],[f527,f476])).
% 2.21/0.67  fof(f527,plain,(
% 2.21/0.67    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(subsumption_resolution,[],[f526,f143])).
% 2.21/0.67  fof(f526,plain,(
% 2.21/0.67    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(subsumption_resolution,[],[f525,f148])).
% 2.21/0.67  fof(f525,plain,(
% 2.21/0.67    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(subsumption_resolution,[],[f524,f153])).
% 2.21/0.67  fof(f524,plain,(
% 2.21/0.67    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_30 | ~spl6_32)),
% 2.21/0.67    inference(subsumption_resolution,[],[f518,f456])).
% 2.21/0.67  fof(f518,plain,(
% 2.21/0.67    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_32),
% 2.21/0.67    inference(superposition,[],[f106,f510])).
% 2.21/0.67  fof(f106,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f42])).
% 2.21/0.67  fof(f2954,plain,(
% 2.21/0.67    ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | spl6_115),
% 2.21/0.67    inference(avatar_component_clause,[],[f2952])).
% 2.21/0.67  fof(f2952,plain,(
% 2.21/0.67    spl6_115 <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).
% 2.21/0.67  fof(f2955,plain,(
% 2.21/0.67    ~spl6_115 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_15 | ~spl6_17 | spl6_34 | ~spl6_36 | ~spl6_41 | ~spl6_48 | ~spl6_68 | ~spl6_72 | ~spl6_77),
% 2.21/0.67    inference(avatar_split_clause,[],[f2949,f1201,f1126,f1060,f694,f634,f597,f547,f300,f274,f166,f151,f146,f141,f2952])).
% 2.21/0.67  fof(f274,plain,(
% 2.21/0.67    spl6_15 <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.21/0.67  fof(f2949,plain,(
% 2.21/0.67    ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_15 | ~spl6_17 | spl6_34 | ~spl6_36 | ~spl6_41 | ~spl6_48 | ~spl6_68 | ~spl6_72 | ~spl6_77)),
% 2.21/0.67    inference(forward_demodulation,[],[f2948,f2715])).
% 2.21/0.67  fof(f2948,plain,(
% 2.21/0.67    ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | (spl6_15 | ~spl6_77)),
% 2.21/0.67    inference(forward_demodulation,[],[f276,f1203])).
% 2.21/0.67  fof(f276,plain,(
% 2.21/0.67    ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) | spl6_15),
% 2.21/0.67    inference(avatar_component_clause,[],[f274])).
% 2.21/0.67  fof(f2931,plain,(
% 2.21/0.67    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_12 | ~spl6_24 | ~spl6_58),
% 2.21/0.67    inference(avatar_contradiction_clause,[],[f2930])).
% 2.21/0.67  fof(f2930,plain,(
% 2.21/0.67    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_12 | ~spl6_24 | ~spl6_58)),
% 2.21/0.67    inference(subsumption_resolution,[],[f2884,f264])).
% 2.21/0.67  fof(f264,plain,(
% 2.21/0.67    ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) | spl6_12),
% 2.21/0.67    inference(avatar_component_clause,[],[f262])).
% 2.21/0.67  fof(f262,plain,(
% 2.21/0.67    spl6_12 <=> v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.21/0.67  fof(f2884,plain,(
% 2.21/0.67    v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_24 | ~spl6_58)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f352,f143,f148,f153,f168,f919,f824])).
% 2.21/0.67  fof(f824,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (~l1_struct_0(k8_tmap_1(X1,X2)) | v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0)) | ~l1_struct_0(X0) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.21/0.67    inference(subsumption_resolution,[],[f823,f115])).
% 2.21/0.67  fof(f115,plain,(
% 2.21/0.67    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f50])).
% 2.21/0.67  fof(f823,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))) | v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0)) | ~l1_struct_0(k8_tmap_1(X1,X2)) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.21/0.67    inference(subsumption_resolution,[],[f822,f86])).
% 2.21/0.67  fof(f86,plain,(
% 2.21/0.67    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f26])).
% 2.21/0.67  fof(f26,plain,(
% 2.21/0.67    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.21/0.67    inference(ennf_transformation,[],[f1])).
% 2.21/0.67  fof(f1,axiom,(
% 2.21/0.67    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.21/0.67  fof(f822,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))) | v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0)) | ~l1_struct_0(k8_tmap_1(X1,X2)) | ~l1_struct_0(X1) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.21/0.67    inference(duplicate_literal_removal,[],[f817])).
% 2.21/0.67  fof(f817,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))) | v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0)) | ~l1_struct_0(k8_tmap_1(X1,X2)) | ~l1_struct_0(X1) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.21/0.67    inference(resolution,[],[f249,f116])).
% 2.21/0.67  fof(f116,plain,(
% 2.21/0.67    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f50])).
% 2.21/0.67  fof(f249,plain,(
% 2.21/0.67    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) | ~l1_struct_0(X0) | ~v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X3),u1_struct_0(X4)) | v1_funct_1(k2_tmap_1(X3,X4,k9_tmap_1(X1,X2),X0)) | ~l1_struct_0(X4) | ~l1_struct_0(X3) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.21/0.67    inference(resolution,[],[f121,f114])).
% 2.21/0.67  fof(f121,plain,(
% 2.21/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f56])).
% 2.21/0.67  fof(f56,plain,(
% 2.21/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.21/0.67    inference(flattening,[],[f55])).
% 2.21/0.67  fof(f55,plain,(
% 2.21/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f10])).
% 2.21/0.67  fof(f10,axiom,(
% 2.21/0.67    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 2.21/0.67  fof(f919,plain,(
% 2.21/0.67    l1_struct_0(k8_tmap_1(sK0,sK1)) | ~spl6_58),
% 2.21/0.67    inference(avatar_component_clause,[],[f917])).
% 2.21/0.67  fof(f917,plain,(
% 2.21/0.67    spl6_58 <=> l1_struct_0(k8_tmap_1(sK0,sK1))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 2.21/0.67  fof(f1204,plain,(
% 2.21/0.67    spl6_77 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30),
% 2.21/0.67    inference(avatar_split_clause,[],[f476,f454,f166,f151,f146,f141,f1201])).
% 2.21/0.67  fof(f1129,plain,(
% 2.21/0.67    spl6_72 | ~spl6_3 | ~spl6_17),
% 2.21/0.67    inference(avatar_split_clause,[],[f305,f300,f151,f1126])).
% 2.21/0.67  fof(f305,plain,(
% 2.21/0.67    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_3 | ~spl6_17)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f153,f302,f89])).
% 2.21/0.67  fof(f1063,plain,(
% 2.21/0.67    spl6_68 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30 | ~spl6_67),
% 2.21/0.67    inference(avatar_split_clause,[],[f1058,f1054,f454,f151,f146,f141,f1060])).
% 2.21/0.67  fof(f1054,plain,(
% 2.21/0.67    spl6_67 <=> v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).
% 2.21/0.67  fof(f1058,plain,(
% 2.21/0.67    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30 | ~spl6_67)),
% 2.21/0.67    inference(forward_demodulation,[],[f1056,f463])).
% 2.21/0.67  fof(f1056,plain,(
% 2.21/0.67    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~spl6_67),
% 2.21/0.67    inference(avatar_component_clause,[],[f1054])).
% 2.21/0.67  fof(f1057,plain,(
% 2.21/0.67    spl6_67 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30),
% 2.21/0.67    inference(avatar_split_clause,[],[f466,f454,f151,f146,f141,f1054])).
% 2.21/0.67  fof(f466,plain,(
% 2.21/0.67    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f143,f148,f153,f456,f117])).
% 2.21/0.67  fof(f117,plain,(
% 2.21/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f52])).
% 2.21/0.67  fof(f1042,plain,(
% 2.21/0.67    spl6_64 | ~spl6_8 | ~spl6_16 | ~spl6_24),
% 2.21/0.67    inference(avatar_split_clause,[],[f441,f350,f295,f176,f1039])).
% 2.21/0.67  fof(f176,plain,(
% 2.21/0.67    spl6_8 <=> r1_tsep_1(sK1,sK2)),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.21/0.67  fof(f441,plain,(
% 2.21/0.67    r1_tsep_1(sK2,sK1) | (~spl6_8 | ~spl6_16 | ~spl6_24)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f297,f178,f352,f120])).
% 2.21/0.67  fof(f120,plain,(
% 2.21/0.67    ( ! [X0,X1] : (~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_tsep_1(X1,X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f54])).
% 2.21/0.67  fof(f54,plain,(
% 2.21/0.67    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.21/0.67    inference(flattening,[],[f53])).
% 2.21/0.67  fof(f53,plain,(
% 2.21/0.67    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f15])).
% 2.21/0.67  fof(f15,axiom,(
% 2.21/0.67    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 2.21/0.67  fof(f178,plain,(
% 2.21/0.67    r1_tsep_1(sK1,sK2) | ~spl6_8),
% 2.21/0.67    inference(avatar_component_clause,[],[f176])).
% 2.21/0.67  fof(f920,plain,(
% 2.21/0.67    spl6_58 | ~spl6_26),
% 2.21/0.67    inference(avatar_split_clause,[],[f427,f360,f917])).
% 2.21/0.67  fof(f360,plain,(
% 2.21/0.67    spl6_26 <=> l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.21/0.67  fof(f427,plain,(
% 2.21/0.67    l1_struct_0(k8_tmap_1(sK0,sK1)) | ~spl6_26),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f362,f86])).
% 2.21/0.67  fof(f362,plain,(
% 2.21/0.67    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl6_26),
% 2.21/0.67    inference(avatar_component_clause,[],[f360])).
% 2.21/0.67  fof(f697,plain,(
% 2.21/0.67    spl6_48 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30 | ~spl6_47),
% 2.21/0.67    inference(avatar_split_clause,[],[f692,f687,f454,f166,f151,f146,f141,f694])).
% 2.21/0.67  fof(f687,plain,(
% 2.21/0.67    spl6_47 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 2.21/0.67  fof(f692,plain,(
% 2.21/0.67    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30 | ~spl6_47)),
% 2.21/0.67    inference(forward_demodulation,[],[f691,f476])).
% 2.21/0.67  fof(f691,plain,(
% 2.21/0.67    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_30 | ~spl6_47)),
% 2.21/0.67    inference(forward_demodulation,[],[f689,f463])).
% 2.21/0.67  fof(f689,plain,(
% 2.21/0.67    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~spl6_47),
% 2.21/0.67    inference(avatar_component_clause,[],[f687])).
% 2.21/0.67  fof(f690,plain,(
% 2.21/0.67    spl6_47 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6),
% 2.21/0.67    inference(avatar_split_clause,[],[f254,f166,f151,f146,f141,f687])).
% 2.21/0.67  fof(f254,plain,(
% 2.21/0.67    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6)),
% 2.21/0.67    inference(forward_demodulation,[],[f251,f215])).
% 2.21/0.67  fof(f251,plain,(
% 2.21/0.67    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f143,f148,f153,f168,f139])).
% 2.21/0.67  fof(f139,plain,(
% 2.21/0.67    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(subsumption_resolution,[],[f138,f114])).
% 2.21/0.67  fof(f138,plain,(
% 2.21/0.67    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(subsumption_resolution,[],[f137,f115])).
% 2.21/0.67  fof(f137,plain,(
% 2.21/0.67    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(subsumption_resolution,[],[f133,f116])).
% 2.21/0.67  fof(f133,plain,(
% 2.21/0.67    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(subsumption_resolution,[],[f129,f89])).
% 2.21/0.67  fof(f129,plain,(
% 2.21/0.67    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(equality_resolution,[],[f128])).
% 2.21/0.67  fof(f128,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(equality_resolution,[],[f96])).
% 2.21/0.67  fof(f96,plain,(
% 2.21/0.67    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f73])).
% 2.21/0.67  fof(f73,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2))) & u1_struct_0(X1) = sK5(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f71,f72])).
% 2.21/0.67  fof(f72,plain,(
% 2.21/0.67    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2))) & u1_struct_0(X1) = sK5(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.21/0.67    introduced(choice_axiom,[])).
% 2.21/0.67  fof(f71,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(rectify,[],[f70])).
% 2.21/0.67  fof(f70,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(nnf_transformation,[],[f36])).
% 2.21/0.67  fof(f36,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(flattening,[],[f35])).
% 2.21/0.67  fof(f35,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f8])).
% 2.21/0.67  fof(f8,axiom,(
% 2.21/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).
% 2.21/0.67  fof(f637,plain,(
% 2.21/0.67    spl6_41 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30 | ~spl6_40),
% 2.21/0.67    inference(avatar_split_clause,[],[f632,f628,f454,f166,f151,f146,f141,f634])).
% 2.21/0.67  fof(f628,plain,(
% 2.21/0.67    spl6_40 <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 2.21/0.67  fof(f632,plain,(
% 2.21/0.67    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30 | ~spl6_40)),
% 2.21/0.67    inference(forward_demodulation,[],[f630,f476])).
% 2.21/0.67  fof(f630,plain,(
% 2.21/0.67    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~spl6_40),
% 2.21/0.67    inference(avatar_component_clause,[],[f628])).
% 2.21/0.67  fof(f631,plain,(
% 2.21/0.67    spl6_40 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6),
% 2.21/0.67    inference(avatar_split_clause,[],[f236,f166,f151,f146,f141,f628])).
% 2.21/0.67  fof(f236,plain,(
% 2.21/0.67    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f143,f148,f153,f168,f116])).
% 2.21/0.67  fof(f600,plain,(
% 2.21/0.67    spl6_36 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30 | ~spl6_35),
% 2.21/0.67    inference(avatar_split_clause,[],[f595,f591,f454,f166,f151,f146,f141,f597])).
% 2.21/0.67  fof(f591,plain,(
% 2.21/0.67    spl6_35 <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 2.21/0.67  fof(f595,plain,(
% 2.21/0.67    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_30 | ~spl6_35)),
% 2.21/0.67    inference(forward_demodulation,[],[f593,f476])).
% 2.21/0.67  fof(f593,plain,(
% 2.21/0.67    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~spl6_35),
% 2.21/0.67    inference(avatar_component_clause,[],[f591])).
% 2.21/0.67  fof(f594,plain,(
% 2.21/0.67    spl6_35 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6),
% 2.21/0.67    inference(avatar_split_clause,[],[f234,f166,f151,f146,f141,f591])).
% 2.21/0.67  fof(f234,plain,(
% 2.21/0.67    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f143,f148,f153,f168,f115])).
% 2.21/0.67  fof(f550,plain,(
% 2.21/0.67    ~spl6_34 | spl6_1 | ~spl6_9),
% 2.21/0.67    inference(avatar_split_clause,[],[f200,f184,f141,f547])).
% 2.21/0.67  fof(f184,plain,(
% 2.21/0.67    spl6_9 <=> l1_struct_0(sK0)),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.21/0.67  fof(f200,plain,(
% 2.21/0.67    ~v1_xboole_0(u1_struct_0(sK0)) | (spl6_1 | ~spl6_9)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f143,f186,f91])).
% 2.21/0.67  fof(f91,plain,(
% 2.21/0.67    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f32])).
% 2.21/0.67  fof(f32,plain,(
% 2.21/0.67    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.21/0.67    inference(flattening,[],[f31])).
% 2.21/0.67  fof(f31,plain,(
% 2.21/0.67    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f4])).
% 2.21/0.67  fof(f4,axiom,(
% 2.21/0.67    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 2.21/0.67  fof(f186,plain,(
% 2.21/0.67    l1_struct_0(sK0) | ~spl6_9),
% 2.21/0.67    inference(avatar_component_clause,[],[f184])).
% 2.21/0.67  fof(f511,plain,(
% 2.21/0.67    spl6_32 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6),
% 2.21/0.67    inference(avatar_split_clause,[],[f215,f166,f151,f146,f141,f508])).
% 2.21/0.67  fof(f457,plain,(
% 2.21/0.67    spl6_30 | ~spl6_3 | ~spl6_6),
% 2.21/0.67    inference(avatar_split_clause,[],[f192,f166,f151,f454])).
% 2.21/0.67  fof(f192,plain,(
% 2.21/0.67    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_3 | ~spl6_6)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f153,f168,f89])).
% 2.21/0.67  fof(f363,plain,(
% 2.21/0.67    spl6_26 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6),
% 2.21/0.67    inference(avatar_split_clause,[],[f208,f166,f151,f146,f141,f360])).
% 2.21/0.67  fof(f208,plain,(
% 2.21/0.67    l1_pre_topc(k8_tmap_1(sK0,sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6)),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f143,f148,f153,f168,f113])).
% 2.21/0.67  fof(f353,plain,(
% 2.21/0.67    spl6_24 | ~spl6_11),
% 2.21/0.67    inference(avatar_split_clause,[],[f290,f245,f350])).
% 2.21/0.67  fof(f245,plain,(
% 2.21/0.67    spl6_11 <=> l1_pre_topc(sK2)),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.21/0.67  fof(f290,plain,(
% 2.21/0.67    l1_struct_0(sK2) | ~spl6_11),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f247,f86])).
% 2.21/0.67  fof(f247,plain,(
% 2.21/0.67    l1_pre_topc(sK2) | ~spl6_11),
% 2.21/0.67    inference(avatar_component_clause,[],[f245])).
% 2.21/0.67  fof(f303,plain,(
% 2.21/0.67    spl6_17 | ~spl6_3),
% 2.21/0.67    inference(avatar_split_clause,[],[f181,f151,f300])).
% 2.21/0.67  fof(f181,plain,(
% 2.21/0.67    m1_pre_topc(sK0,sK0) | ~spl6_3),
% 2.21/0.67    inference(unit_resulting_resolution,[],[f153,f87])).
% 2.21/0.67  fof(f87,plain,(
% 2.21/0.67    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f27])).
% 2.21/0.68  fof(f27,plain,(
% 2.21/0.68    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.21/0.68    inference(ennf_transformation,[],[f19])).
% 2.21/0.68  fof(f19,axiom,(
% 2.21/0.68    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.21/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.21/0.68  fof(f298,plain,(
% 2.21/0.68    spl6_16 | ~spl6_10),
% 2.21/0.68    inference(avatar_split_clause,[],[f255,f228,f295])).
% 2.21/0.68  fof(f228,plain,(
% 2.21/0.68    spl6_10 <=> l1_pre_topc(sK1)),
% 2.21/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.21/0.68  fof(f255,plain,(
% 2.21/0.68    l1_struct_0(sK1) | ~spl6_10),
% 2.21/0.68    inference(unit_resulting_resolution,[],[f230,f86])).
% 2.21/0.68  fof(f230,plain,(
% 2.21/0.68    l1_pre_topc(sK1) | ~spl6_10),
% 2.21/0.68    inference(avatar_component_clause,[],[f228])).
% 2.21/0.68  fof(f277,plain,(
% 2.21/0.68    ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15),
% 2.21/0.68    inference(avatar_split_clause,[],[f83,f274,f270,f266,f262])).
% 2.21/0.68  fof(f83,plain,(
% 2.21/0.68    ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))),
% 2.21/0.68    inference(cnf_transformation,[],[f62])).
% 2.21/0.68  fof(f62,plain,(
% 2.21/0.68    (((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))) & r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.21/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f61,f60,f59])).
% 2.21/0.68  fof(f59,plain,(
% 2.21/0.68    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X2,k8_tmap_1(sK0,X1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.21/0.68    introduced(choice_axiom,[])).
% 2.21/0.68  fof(f60,plain,(
% 2.21/0.68    ? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X2,k8_tmap_1(sK0,X1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,X1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X2,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2))) & r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 2.21/0.68    introduced(choice_axiom,[])).
% 2.21/0.68  fof(f61,plain,(
% 2.21/0.68    ? [X2] : ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X2,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2))) & r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK2,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2))) & r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 2.21/0.68    introduced(choice_axiom,[])).
% 2.21/0.68  fof(f24,plain,(
% 2.21/0.68    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.21/0.68    inference(flattening,[],[f23])).
% 2.21/0.68  fof(f23,plain,(
% 2.21/0.68    ? [X0] : (? [X1] : (? [X2] : (((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.21/0.68    inference(ennf_transformation,[],[f22])).
% 2.21/0.68  fof(f22,negated_conjecture,(
% 2.21/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)))))))),
% 2.21/0.68    inference(negated_conjecture,[],[f21])).
% 2.21/0.68  fof(f21,conjecture,(
% 2.21/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)))))))),
% 2.21/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_tmap_1)).
% 2.21/0.68  fof(f248,plain,(
% 2.21/0.68    spl6_11 | ~spl6_3 | ~spl6_7),
% 2.21/0.68    inference(avatar_split_clause,[],[f189,f171,f151,f245])).
% 2.21/0.68  fof(f189,plain,(
% 2.21/0.68    l1_pre_topc(sK2) | (~spl6_3 | ~spl6_7)),
% 2.21/0.68    inference(unit_resulting_resolution,[],[f173,f153,f88])).
% 2.21/0.68  fof(f88,plain,(
% 2.21/0.68    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f28])).
% 2.21/0.68  fof(f28,plain,(
% 2.21/0.68    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.21/0.68    inference(ennf_transformation,[],[f2])).
% 2.21/0.68  fof(f2,axiom,(
% 2.21/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.21/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.21/0.68  fof(f231,plain,(
% 2.21/0.68    spl6_10 | ~spl6_3 | ~spl6_6),
% 2.21/0.68    inference(avatar_split_clause,[],[f188,f166,f151,f228])).
% 2.21/0.68  fof(f188,plain,(
% 2.21/0.68    l1_pre_topc(sK1) | (~spl6_3 | ~spl6_6)),
% 2.21/0.68    inference(unit_resulting_resolution,[],[f168,f153,f88])).
% 2.21/0.68  fof(f187,plain,(
% 2.21/0.68    spl6_9 | ~spl6_3),
% 2.21/0.68    inference(avatar_split_clause,[],[f180,f151,f184])).
% 2.21/0.68  fof(f180,plain,(
% 2.21/0.68    l1_struct_0(sK0) | ~spl6_3),
% 2.21/0.68    inference(unit_resulting_resolution,[],[f153,f86])).
% 2.21/0.68  fof(f179,plain,(
% 2.21/0.68    spl6_8),
% 2.21/0.68    inference(avatar_split_clause,[],[f82,f176])).
% 2.21/0.68  fof(f82,plain,(
% 2.21/0.68    r1_tsep_1(sK1,sK2)),
% 2.21/0.68    inference(cnf_transformation,[],[f62])).
% 2.21/0.68  fof(f174,plain,(
% 2.21/0.68    spl6_7),
% 2.21/0.68    inference(avatar_split_clause,[],[f81,f171])).
% 2.21/0.68  fof(f81,plain,(
% 2.21/0.68    m1_pre_topc(sK2,sK0)),
% 2.21/0.68    inference(cnf_transformation,[],[f62])).
% 2.21/0.68  fof(f169,plain,(
% 2.21/0.68    spl6_6),
% 2.21/0.68    inference(avatar_split_clause,[],[f79,f166])).
% 2.21/0.68  fof(f79,plain,(
% 2.21/0.68    m1_pre_topc(sK1,sK0)),
% 2.21/0.68    inference(cnf_transformation,[],[f62])).
% 2.21/0.68  fof(f164,plain,(
% 2.21/0.68    ~spl6_5),
% 2.21/0.68    inference(avatar_split_clause,[],[f80,f161])).
% 2.21/0.68  fof(f80,plain,(
% 2.21/0.68    ~v2_struct_0(sK2)),
% 2.21/0.68    inference(cnf_transformation,[],[f62])).
% 2.21/0.68  fof(f154,plain,(
% 2.21/0.68    spl6_3),
% 2.21/0.68    inference(avatar_split_clause,[],[f77,f151])).
% 2.21/0.68  fof(f77,plain,(
% 2.21/0.68    l1_pre_topc(sK0)),
% 2.21/0.68    inference(cnf_transformation,[],[f62])).
% 2.21/0.68  fof(f149,plain,(
% 2.21/0.68    spl6_2),
% 2.21/0.68    inference(avatar_split_clause,[],[f76,f146])).
% 2.21/0.68  fof(f76,plain,(
% 2.21/0.68    v2_pre_topc(sK0)),
% 2.21/0.68    inference(cnf_transformation,[],[f62])).
% 2.21/0.68  fof(f144,plain,(
% 2.21/0.68    ~spl6_1),
% 2.21/0.68    inference(avatar_split_clause,[],[f75,f141])).
% 2.21/0.68  fof(f75,plain,(
% 2.21/0.68    ~v2_struct_0(sK0)),
% 2.21/0.68    inference(cnf_transformation,[],[f62])).
% 2.21/0.68  % SZS output end Proof for theBenchmark
% 2.21/0.68  % (21705)------------------------------
% 2.21/0.68  % (21705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.68  % (21705)Termination reason: Refutation
% 2.21/0.68  
% 2.21/0.68  % (21705)Memory used [KB]: 13688
% 2.21/0.68  % (21705)Time elapsed: 0.232 s
% 2.21/0.68  % (21705)------------------------------
% 2.21/0.68  % (21705)------------------------------
% 2.21/0.68  % (21681)Success in time 0.321 s
%------------------------------------------------------------------------------
