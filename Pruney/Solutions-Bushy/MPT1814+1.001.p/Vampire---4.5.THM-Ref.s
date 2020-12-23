%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1814+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  433 (2163 expanded)
%              Number of leaves         :   15 ( 489 expanded)
%              Depth                    :   36
%              Number of atoms          : 3815 (35460 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   29 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1573,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f105,f110,f115,f154,f178,f182,f189,f191,f193,f488,f527,f554,f556,f584,f668,f669,f711,f737,f760,f799,f811,f831,f833,f972,f988,f1021,f1039,f1068,f1094,f1139,f1194,f1231,f1255,f1257,f1366,f1450,f1452,f1454,f1565,f1572])).

fof(f1572,plain,
    ( spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1571,f73,f92])).

fof(f92,plain,
    ( spl5_5
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f73,plain,
    ( spl5_1
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1571,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f37,f74])).

fof(f74,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f37,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & v1_borsuk_1(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_borsuk_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_tmap_1)).

fof(f1565,plain,
    ( spl5_12
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1455,f73,f151])).

fof(f151,plain,
    ( spl5_12
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1455,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f38,f74])).

fof(f38,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f6])).

fof(f1454,plain,
    ( spl5_7
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1453,f73,f102])).

fof(f102,plain,
    ( spl5_7
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1453,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f41,f74])).

fof(f41,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f6])).

fof(f1452,plain,
    ( spl5_10
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1451,f73,f143])).

fof(f143,plain,
    ( spl5_10
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f1451,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f42,f74])).

fof(f42,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f6])).

fof(f1450,plain,
    ( spl5_11
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1449,f73,f147])).

fof(f147,plain,
    ( spl5_11
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1449,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f40,f74])).

fof(f40,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f6])).

fof(f1366,plain,
    ( spl5_6
    | spl5_2 ),
    inference(avatar_split_clause,[],[f1365,f77,f97])).

fof(f97,plain,
    ( spl5_6
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f77,plain,
    ( spl5_2
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1365,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f27,f78])).

fof(f78,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f27,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1257,plain,
    ( spl5_7
    | spl5_4 ),
    inference(avatar_split_clause,[],[f1256,f87,f102])).

fof(f87,plain,
    ( spl5_4
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1256,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f25,f88])).

fof(f88,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f25,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f1255,plain,
    ( spl5_10
    | spl5_4 ),
    inference(avatar_split_clause,[],[f1232,f87,f143])).

fof(f1232,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | spl5_4 ),
    inference(subsumption_resolution,[],[f26,f88])).

fof(f26,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f1231,plain,
    ( spl5_12
    | spl5_4 ),
    inference(avatar_split_clause,[],[f1230,f87,f151])).

fof(f1230,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl5_4 ),
    inference(subsumption_resolution,[],[f22,f88])).

fof(f22,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f1194,plain,
    ( spl5_4
    | spl5_11 ),
    inference(avatar_split_clause,[],[f1193,f147,f87])).

fof(f1193,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | spl5_11 ),
    inference(subsumption_resolution,[],[f24,f149])).

fof(f149,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f24,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f1139,plain,
    ( spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f1138,f77,f87])).

fof(f1138,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f19,f78])).

fof(f19,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f1094,plain,
    ( spl5_4
    | spl5_9 ),
    inference(avatar_split_clause,[],[f1093,f112,f87])).

fof(f112,plain,
    ( spl5_9
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1093,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f20,f113])).

fof(f113,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f20,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f1068,plain,
    ( spl5_9
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1040,f73,f112])).

fof(f1040,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f36,f74])).

fof(f36,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f6])).

fof(f1039,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f1038])).

fof(f1038,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1037,f74])).

fof(f1037,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1036,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f1036,plain,
    ( v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1035,f104])).

fof(f104,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f1035,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1034,f148])).

fof(f148,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f1034,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1033,f84])).

fof(f84,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_3
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1033,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1032,f152])).

fof(f152,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f1032,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f1031,f94])).

fof(f94,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f1031,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f1030,f114])).

fof(f114,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f1030,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f1029,f79])).

fof(f79,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f1029,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f1028,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f1028,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f1027,f51])).

fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1027,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f1026,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f1026,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f1025,f55])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f1025,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f836,f54])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f836,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_10 ),
    inference(resolution,[],[f144,f221])).

fof(f221,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | v2_struct_0(X4)
      | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4))) ) ),
    inference(subsumption_resolution,[],[f220,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f220,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4))) ) ),
    inference(subsumption_resolution,[],[f219,f46])).

fof(f46,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f219,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4))) ) ),
    inference(subsumption_resolution,[],[f218,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f6])).

fof(f218,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4))) ) ),
    inference(subsumption_resolution,[],[f217,f49])).

fof(f49,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f217,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4))) ) ),
    inference(subsumption_resolution,[],[f216,f47])).

% (15669)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f216,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4))) ) ),
    inference(subsumption_resolution,[],[f215,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f215,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4))) ) ),
    inference(subsumption_resolution,[],[f199,f57])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f199,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4))) ) ),
    inference(resolution,[],[f62,f132])).

fof(f132,plain,(
    r4_tsep_1(sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f130,f46])).

fof(f130,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | r4_tsep_1(sK0,sK3,sK4) ),
    inference(resolution,[],[f125,f45])).

fof(f45,plain,(
    v1_borsuk_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f125,plain,(
    ! [X1] :
      ( ~ v1_borsuk_1(X1,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | r4_tsep_1(sK0,sK3,X1) ) ),
    inference(subsumption_resolution,[],[f124,f49])).

fof(f124,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK3,sK0)
      | ~ v1_borsuk_1(X1,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | r4_tsep_1(sK0,sK3,X1) ) ),
    inference(subsumption_resolution,[],[f123,f56])).

fof(f123,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_borsuk_1(X1,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | r4_tsep_1(sK0,sK3,X1) ) ),
    inference(subsumption_resolution,[],[f122,f58])).

fof(f122,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_borsuk_1(X1,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | r4_tsep_1(sK0,sK3,X1) ) ),
    inference(subsumption_resolution,[],[f117,f57])).

fof(f117,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_borsuk_1(X1,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | r4_tsep_1(sK0,sK3,X1) ) ),
    inference(resolution,[],[f71,f48])).

fof(f48,plain,(
    v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f6])).

% (15668)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_borsuk_1(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | r4_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_borsuk_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tsep_1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r4_tsep_1(X0,X2,X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).

fof(f144,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f1021,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f1020])).

fof(f1020,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1019,f88])).

fof(f1019,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1000,f94])).

fof(f1000,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f999,f53])).

fof(f999,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f998,f104])).

fof(f998,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f997,f148])).

fof(f997,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f996,f84])).

fof(f996,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f995,f152])).

fof(f995,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f994,f114])).

fof(f994,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f993,f79])).

fof(f993,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f992,f52])).

fof(f992,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f991,f51])).

fof(f991,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f990,f50])).

fof(f990,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f989,f55])).

fof(f989,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f839,f54])).

fof(f839,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f144,f261])).

fof(f261,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | v2_struct_0(X4)
      | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4) ) ),
    inference(subsumption_resolution,[],[f260,f56])).

fof(f260,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4) ) ),
    inference(subsumption_resolution,[],[f259,f46])).

fof(f259,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4) ) ),
    inference(subsumption_resolution,[],[f258,f44])).

fof(f258,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4) ) ),
    inference(subsumption_resolution,[],[f257,f49])).

fof(f257,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4) ) ),
    inference(subsumption_resolution,[],[f256,f47])).

fof(f256,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4) ) ),
    inference(subsumption_resolution,[],[f255,f58])).

fof(f255,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4) ) ),
    inference(subsumption_resolution,[],[f239,f57])).

fof(f239,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4) ) ),
    inference(resolution,[],[f60,f132])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r4_tsep_1(X0,X2,X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f988,plain,
    ( spl5_5
    | spl5_8 ),
    inference(avatar_split_clause,[],[f983,f107,f92])).

fof(f107,plain,
    ( spl5_8
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f983,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f13,f108])).

fof(f108,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f13,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f972,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f971])).

fof(f971,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f970,f108])).

fof(f970,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f969,f53])).

fof(f969,plain,
    ( v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f968,f104])).

fof(f968,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f967,f148])).

fof(f967,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f966,f84])).

fof(f966,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f965,f152])).

fof(f965,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f964,f94])).

fof(f964,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f963,f114])).

fof(f963,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f962,f79])).

fof(f962,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f961,f52])).

fof(f961,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f960,f51])).

fof(f960,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f959,f50])).

fof(f959,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f958,f55])).

fof(f958,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f957,f54])).

fof(f957,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_10 ),
    inference(resolution,[],[f401,f144])).

fof(f401,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | v2_struct_0(X4)
      | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)))) ) ),
    inference(subsumption_resolution,[],[f400,f56])).

fof(f400,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)))) ) ),
    inference(subsumption_resolution,[],[f399,f46])).

fof(f399,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)))) ) ),
    inference(subsumption_resolution,[],[f398,f44])).

fof(f398,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)))) ) ),
    inference(subsumption_resolution,[],[f397,f49])).

fof(f397,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)))) ) ),
    inference(subsumption_resolution,[],[f396,f47])).

fof(f396,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)))) ) ),
    inference(subsumption_resolution,[],[f395,f58])).

fof(f395,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)))) ) ),
    inference(subsumption_resolution,[],[f379,f57])).

fof(f379,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)))) ) ),
    inference(resolution,[],[f59,f132])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r4_tsep_1(X0,X2,X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f833,plain,
    ( spl5_10
    | spl5_8 ),
    inference(avatar_split_clause,[],[f832,f107,f143])).

fof(f832,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | spl5_8 ),
    inference(subsumption_resolution,[],[f18,f108])).

fof(f18,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f831,plain,
    ( spl5_11
    | spl5_8 ),
    inference(avatar_split_clause,[],[f830,f107,f147])).

fof(f830,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | spl5_8 ),
    inference(subsumption_resolution,[],[f16,f108])).

fof(f16,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f811,plain,
    ( spl5_2
    | spl5_8 ),
    inference(avatar_split_clause,[],[f810,f107,f77])).

fof(f810,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl5_8 ),
    inference(subsumption_resolution,[],[f11,f108])).

fof(f11,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f799,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f798])).

fof(f798,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f789,f78])).

fof(f789,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f788,f56])).

fof(f788,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f787,f89])).

fof(f89,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f787,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f786,f99])).

fof(f99,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f786,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f785,f75])).

fof(f75,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f785,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f784,f52])).

fof(f784,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f783,f51])).

fof(f783,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f782,f50])).

fof(f782,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f781,f132])).

fof(f781,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f780,f46])).

fof(f780,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f779,f44])).

fof(f779,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f778,f49])).

fof(f778,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f777,f47])).

fof(f777,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f776,f55])).

fof(f776,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f775,f54])).

fof(f775,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f774,f53])).

fof(f774,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f773,f58])).

fof(f773,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f585,f57])).

fof(f585,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f109,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f109,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f760,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f759])).

fof(f759,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f758,f103])).

fof(f103,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f758,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f757,f56])).

fof(f757,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f756,f89])).

fof(f756,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f755,f99])).

fof(f755,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f754,f75])).

fof(f754,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f753,f52])).

fof(f753,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f752,f51])).

fof(f752,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f751,f50])).

fof(f751,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f750,f132])).

fof(f750,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f749,f46])).

fof(f749,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f748,f44])).

fof(f748,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f747,f49])).

fof(f747,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f746,f47])).

fof(f746,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f745,f55])).

fof(f745,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f744,f54])).

fof(f744,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f743,f53])).

fof(f743,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f742,f58])).

fof(f742,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f591,f57])).

fof(f591,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f109,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f737,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f736])).

fof(f736,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | spl5_11 ),
    inference(subsumption_resolution,[],[f735,f149])).

fof(f735,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f734,f56])).

fof(f734,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f733,f89])).

fof(f733,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f732,f99])).

fof(f732,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f731,f75])).

fof(f731,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f730,f52])).

fof(f730,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f729,f51])).

fof(f729,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f728,f50])).

fof(f728,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f727,f132])).

fof(f727,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f726,f46])).

fof(f726,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f725,f44])).

fof(f725,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f724,f49])).

fof(f724,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f723,f47])).

fof(f723,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f722,f55])).

fof(f722,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f721,f54])).

fof(f721,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f720,f53])).

fof(f720,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f719,f58])).

fof(f719,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f590,f57])).

fof(f590,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f109,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f711,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f710])).

fof(f710,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | spl5_10 ),
    inference(subsumption_resolution,[],[f667,f145])).

fof(f145,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f667,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f666,f56])).

fof(f666,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f665,f89])).

fof(f665,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f664,f99])).

fof(f664,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f663,f75])).

fof(f663,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f662,f52])).

fof(f662,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f661,f51])).

fof(f661,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f660,f50])).

fof(f660,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f659,f132])).

fof(f659,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f658,f46])).

fof(f658,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f657,f44])).

fof(f657,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f656,f49])).

fof(f656,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f655,f47])).

fof(f655,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f654,f55])).

fof(f654,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f653,f54])).

fof(f653,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f652,f53])).

fof(f652,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f651,f58])).

fof(f651,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f592,f57])).

fof(f592,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f109,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f669,plain,
    ( spl5_12
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f644,f107,f97,f87,f73,f151])).

fof(f644,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f643,f56])).

fof(f643,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f642,f89])).

fof(f642,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f641,f99])).

fof(f641,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f605,f75])).

fof(f605,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f604,f52])).

fof(f604,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f603,f51])).

fof(f603,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f602,f50])).

fof(f602,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f601,f132])).

fof(f601,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f600,f46])).

fof(f600,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f599,f44])).

fof(f599,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f598,f49])).

fof(f598,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f597,f47])).

fof(f597,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f596,f55])).

fof(f596,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f595,f54])).

fof(f595,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f594,f53])).

fof(f594,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f593,f58])).

fof(f593,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f588,f57])).

fof(f588,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f109,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f668,plain,
    ( spl5_5
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f628,f107,f97,f87,f73,f92])).

fof(f628,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f627,f56])).

fof(f627,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f626,f89])).

fof(f626,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f625,f99])).

fof(f625,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f624,f75])).

fof(f624,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f623,f52])).

fof(f623,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f622,f51])).

fof(f622,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f621,f50])).

fof(f621,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f620,f132])).

fof(f620,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f619,f46])).

fof(f619,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f618,f44])).

fof(f618,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f617,f49])).

fof(f617,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f616,f47])).

fof(f616,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f615,f55])).

fof(f615,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f614,f54])).

fof(f614,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f613,f53])).

fof(f613,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f612,f58])).

fof(f612,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f587,f57])).

fof(f587,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f109,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f584,plain,
    ( spl5_8
    | spl5_12 ),
    inference(avatar_split_clause,[],[f583,f151,f107])).

fof(f583,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | spl5_12 ),
    inference(subsumption_resolution,[],[f14,f153])).

fof(f153,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f14,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f556,plain,
    ( spl5_8
    | spl5_3 ),
    inference(avatar_split_clause,[],[f555,f82,f107])).

fof(f555,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | spl5_3 ),
    inference(subsumption_resolution,[],[f15,f83])).

fof(f83,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f15,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f554,plain,
    ( ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f552,f99])).

fof(f552,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f551,f83])).

fof(f551,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f550,f56])).

fof(f550,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f549,f89])).

fof(f549,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f548,f75])).

fof(f548,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f547,f52])).

fof(f547,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f546,f51])).

fof(f546,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f545,f50])).

fof(f545,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f544,f132])).

fof(f544,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f543,f46])).

fof(f543,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f542,f44])).

fof(f542,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f541,f49])).

fof(f541,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f540,f47])).

fof(f540,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f539,f55])).

fof(f539,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f538,f54])).

fof(f538,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f537,f53])).

fof(f537,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f536,f58])).

fof(f536,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f156,f57])).

fof(f156,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f67,f109])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f527,plain,
    ( spl5_3
    | spl5_6 ),
    inference(avatar_split_clause,[],[f526,f97,f82])).

fof(f526,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | spl5_6 ),
    inference(subsumption_resolution,[],[f31,f98])).

fof(f98,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f31,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f488,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f486,f98])).

fof(f486,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f485,f53])).

fof(f485,plain,
    ( v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f484,f104])).

fof(f484,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f483,f148])).

fof(f483,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f482,f84])).

fof(f482,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f481,f152])).

fof(f481,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f480,f94])).

fof(f480,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f479,f114])).

fof(f479,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f478,f79])).

fof(f478,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f477,f52])).

fof(f477,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f476,f51])).

fof(f476,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f475,f50])).

fof(f475,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f474,f55])).

fof(f474,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f473,f54])).

fof(f473,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_10 ),
    inference(resolution,[],[f335,f144])).

fof(f335,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | v2_struct_0(X4)
      | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f334,f56])).

fof(f334,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f333,f46])).

fof(f333,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f332,f44])).

fof(f332,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f331,f49])).

fof(f331,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f330,f47])).

fof(f330,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f329,f58])).

fof(f329,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f313,f57])).

fof(f313,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4)
      | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4))))
      | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4)) ) ),
    inference(resolution,[],[f61,f132])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r4_tsep_1(X0,X2,X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f193,plain,
    ( spl5_10
    | spl5_6 ),
    inference(avatar_split_clause,[],[f192,f97,f143])).

fof(f192,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | spl5_6 ),
    inference(subsumption_resolution,[],[f34,f98])).

fof(f34,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f191,plain,
    ( spl5_12
    | spl5_6 ),
    inference(avatar_split_clause,[],[f190,f97,f151])).

fof(f190,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl5_6 ),
    inference(subsumption_resolution,[],[f30,f98])).

fof(f30,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f189,plain,
    ( spl5_11
    | spl5_6 ),
    inference(avatar_split_clause,[],[f188,f97,f147])).

fof(f188,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | spl5_6 ),
    inference(subsumption_resolution,[],[f32,f98])).

fof(f32,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f182,plain,
    ( spl5_6
    | spl5_9 ),
    inference(avatar_split_clause,[],[f181,f112,f97])).

fof(f181,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | spl5_9 ),
    inference(subsumption_resolution,[],[f28,f113])).

fof(f28,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f178,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f176,f56])).

fof(f176,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f175,f89])).

fof(f175,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f174,f99])).

% (15680)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
fof(f174,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f173,f75])).

fof(f173,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f172,f113])).

fof(f172,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f171,f52])).

fof(f171,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f170,f51])).

fof(f170,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f169,f50])).

fof(f169,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f168,f132])).

fof(f168,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f167,f46])).

fof(f167,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f166,f44])).

fof(f166,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f165,f49])).

fof(f165,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f164,f47])).

fof(f164,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f163,f55])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f162,f54])).

fof(f162,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f161,f53])).

fof(f161,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f160,f58])).

fof(f160,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f159,f57])).

fof(f159,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f64,f109])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f154,plain,
    ( ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_9
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f141,f107,f102,f97,f92,f87,f82,f77,f73,f112,f151,f147,f143])).

fof(f141,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f140,f109])).

fof(f140,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f139,f89])).

fof(f139,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f138,f99])).

fof(f138,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f137,f75])).

fof(f137,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f136,f104])).

fof(f136,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f135,f84])).

fof(f135,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f134,f94])).

fof(f134,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f43,f79])).

fof(f43,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f115,plain,
    ( spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f12,f112,f107])).

fof(f12,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f110,plain,
    ( spl5_8
    | spl5_7 ),
    inference(avatar_split_clause,[],[f17,f102,f107])).

fof(f17,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f105,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f33,f102,f97])).

fof(f33,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f100,plain,
    ( spl5_6
    | spl5_5 ),
    inference(avatar_split_clause,[],[f29,f92,f97])).

fof(f29,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f95,plain,
    ( spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f21,f92,f87])).

fof(f21,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f90,plain,
    ( spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f23,f82,f87])).

fof(f23,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f39,f82,f73])).

fof(f39,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f6])).

fof(f80,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f35,f77,f73])).

fof(f35,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
