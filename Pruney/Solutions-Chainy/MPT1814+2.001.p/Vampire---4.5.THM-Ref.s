%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_tmap_1)).

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

% (14606)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
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

% (14591)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tsep_1)).

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

% (14600)WARNING: option uwaf not known.
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_tmap_1)).

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

% (14600)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
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

% (14592)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
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

% (14596)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
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

% (14611)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
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

% (14599)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
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

fof(f174,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f173,f75])).

% (14604)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
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

% (14590)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
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
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:08:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (14603)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.48  % (14605)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % (14595)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.49  % (14605)Refutation not found, incomplete strategy% (14605)------------------------------
% 0.22/0.49  % (14605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (14605)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (14605)Memory used [KB]: 1023
% 0.22/0.49  % (14605)Time elapsed: 0.010 s
% 0.22/0.49  % (14605)------------------------------
% 0.22/0.49  % (14605)------------------------------
% 0.22/0.50  % (14601)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.50  % (14602)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.51  % (14589)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (14593)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.51  % (14610)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.22/0.51  % (14607)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.22/0.51  % (14594)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.51  % (14608)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (14595)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f1573,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f105,f110,f115,f154,f178,f182,f189,f191,f193,f488,f527,f554,f556,f584,f668,f669,f711,f737,f760,f799,f811,f831,f833,f972,f988,f1021,f1039,f1068,f1094,f1139,f1194,f1231,f1255,f1257,f1366,f1450,f1452,f1454,f1565,f1572])).
% 0.22/0.52  fof(f1572,plain,(
% 0.22/0.52    spl5_5 | spl5_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f1571,f73,f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl5_5 <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl5_1 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.52  fof(f1571,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | spl5_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f37,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | spl5_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f73])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f5])).
% 0.22/0.52  fof(f5,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f3])).
% 0.22/0.52  fof(f3,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_tmap_1)).
% 0.22/0.52  fof(f1565,plain,(
% 0.22/0.52    spl5_12 | spl5_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f1455,f73,f151])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    spl5_12 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.52  fof(f1455,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl5_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f38,f74])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1454,plain,(
% 0.22/0.52    spl5_7 | spl5_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f1453,f73,f102])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    spl5_7 <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.52  fof(f1453,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | spl5_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f41,f74])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1452,plain,(
% 0.22/0.52    spl5_10 | spl5_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f1451,f73,f143])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    spl5_10 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.52  fof(f1451,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | spl5_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f42,f74])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1450,plain,(
% 0.22/0.52    spl5_11 | spl5_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f1449,f73,f147])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    spl5_11 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.52  % (14606)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.52  fof(f1449,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | spl5_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f40,f74])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1366,plain,(
% 0.22/0.52    spl5_6 | spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f1365,f77,f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    spl5_6 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl5_2 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.52  fof(f1365,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | spl5_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f27,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl5_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f77])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1257,plain,(
% 0.22/0.52    spl5_7 | spl5_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f1256,f87,f102])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl5_4 <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.52  fof(f1256,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | spl5_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f25,f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | spl5_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f87])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1255,plain,(
% 0.22/0.52    spl5_10 | spl5_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f1232,f87,f143])).
% 0.22/0.52  fof(f1232,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | spl5_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f26,f88])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1231,plain,(
% 0.22/0.52    spl5_12 | spl5_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f1230,f87,f151])).
% 0.22/0.52  fof(f1230,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl5_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f22,f88])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1194,plain,(
% 0.22/0.52    spl5_4 | spl5_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f1193,f147,f87])).
% 0.22/0.52  fof(f1193,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | spl5_11),
% 0.22/0.52    inference(subsumption_resolution,[],[f24,f149])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | spl5_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f147])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1139,plain,(
% 0.22/0.52    spl5_4 | spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f1138,f77,f87])).
% 0.22/0.52  fof(f1138,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | spl5_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f19,f78])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1094,plain,(
% 0.22/0.52    spl5_4 | spl5_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f1093,f112,f87])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    spl5_9 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.52  fof(f1093,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | spl5_9),
% 0.22/0.52    inference(subsumption_resolution,[],[f20,f113])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | spl5_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f112])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1068,plain,(
% 0.22/0.52    spl5_9 | spl5_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f1040,f73,f112])).
% 0.22/0.52  fof(f1040,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | spl5_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f36,f74])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1039,plain,(
% 0.22/0.52    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1038])).
% 0.22/0.52  fof(f1038,plain,(
% 0.22/0.52    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1037,f74])).
% 0.22/0.52  fof(f1037,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1036,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ~v2_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1036,plain,(
% 0.22/0.52    v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1035,f104])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~spl5_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f102])).
% 0.22/0.52  fof(f1035,plain,(
% 0.22/0.52    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1034,f148])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~spl5_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f147])).
% 0.22/0.52  fof(f1034,plain,(
% 0.22/0.52    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_9 | ~spl5_10 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1033,f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~spl5_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl5_3 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.52  fof(f1033,plain,(
% 0.22/0.52    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | (~spl5_2 | ~spl5_5 | ~spl5_9 | ~spl5_10 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1032,f152])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl5_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f151])).
% 0.22/0.52  fof(f1032,plain,(
% 0.22/0.52    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | (~spl5_2 | ~spl5_5 | ~spl5_9 | ~spl5_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1031,f94])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~spl5_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f92])).
% 0.22/0.52  fof(f1031,plain,(
% 0.22/0.52    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | (~spl5_2 | ~spl5_9 | ~spl5_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1030,f114])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl5_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f112])).
% 0.22/0.52  fof(f1030,plain,(
% 0.22/0.52    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | (~spl5_2 | ~spl5_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1029,f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~spl5_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f77])).
% 0.22/0.52  fof(f1029,plain,(
% 0.22/0.52    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f1028,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1028,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f1027,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1027,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f1026,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1026,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f1025,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    l1_pre_topc(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f1025,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f836,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    v2_pre_topc(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f836,plain,(
% 0.22/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~spl5_10),
% 0.22/0.52    inference(resolution,[],[f144,f221])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    ( ! [X4,X5] : (~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | v2_struct_0(X4) | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f220,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f219,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    m1_pre_topc(sK4,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f219,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f218,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ~v2_struct_0(sK4)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f217,f49])).
% 0.22/0.52  % (14591)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    m1_pre_topc(sK3,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f216,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ~v2_struct_0(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f216,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f215,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    ( ! [X4,X5] : (~l1_pre_topc(sK0) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f199,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    ( ! [X4,X5] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)))) )),
% 0.22/0.52    inference(resolution,[],[f62,f132])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f130,f46])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    ~m1_pre_topc(sK4,sK0) | r4_tsep_1(sK0,sK3,sK4)),
% 0.22/0.52    inference(resolution,[],[f125,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    v1_borsuk_1(sK4,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    ( ! [X1] : (~v1_borsuk_1(X1,sK0) | ~m1_pre_topc(X1,sK0) | r4_tsep_1(sK0,sK3,X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f124,f49])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    ( ! [X1] : (~m1_pre_topc(sK3,sK0) | ~v1_borsuk_1(X1,sK0) | ~m1_pre_topc(X1,sK0) | r4_tsep_1(sK0,sK3,X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f123,f56])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ( ! [X1] : (v2_struct_0(sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_borsuk_1(X1,sK0) | ~m1_pre_topc(X1,sK0) | r4_tsep_1(sK0,sK3,X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f122,f58])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    ( ! [X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_borsuk_1(X1,sK0) | ~m1_pre_topc(X1,sK0) | r4_tsep_1(sK0,sK3,X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f117,f57])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_borsuk_1(X1,sK0) | ~m1_pre_topc(X1,sK0) | r4_tsep_1(sK0,sK3,X1)) )),
% 0.22/0.52    inference(resolution,[],[f71,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    v1_borsuk_1(sK3,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_borsuk_1(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X2,X0) | r4_tsep_1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tsep_1)).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (~r4_tsep_1(X0,X2,X3) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f7])).
% 0.22/0.52  % (14600)WARNING: option uwaf not known.
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_tmap_1)).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~spl5_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f143])).
% 0.22/0.52  fof(f1021,plain,(
% 0.22/0.52    ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1020])).
% 0.22/0.52  fof(f1020,plain,(
% 0.22/0.52    $false | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1019,f88])).
% 0.22/0.52  fof(f1019,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1000,f94])).
% 0.22/0.52  fof(f1000,plain,(
% 0.22/0.52    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f999,f53])).
% 0.22/0.52  fof(f999,plain,(
% 0.22/0.52    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | v2_struct_0(sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f998,f104])).
% 0.22/0.52  fof(f998,plain,(
% 0.22/0.52    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f997,f148])).
% 0.22/0.52  fof(f997,plain,(
% 0.22/0.52    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_9 | ~spl5_10 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f996,f84])).
% 0.22/0.52  fof(f996,plain,(
% 0.22/0.52    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | (~spl5_2 | ~spl5_9 | ~spl5_10 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f995,f152])).
% 0.22/0.52  fof(f995,plain,(
% 0.22/0.52    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | (~spl5_2 | ~spl5_9 | ~spl5_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f994,f114])).
% 0.22/0.52  fof(f994,plain,(
% 0.22/0.52    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | (~spl5_2 | ~spl5_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f993,f79])).
% 0.22/0.52  fof(f993,plain,(
% 0.22/0.52    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f992,f52])).
% 0.22/0.52  fof(f992,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f991,f51])).
% 0.22/0.52  fof(f991,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f990,f50])).
% 0.22/0.52  fof(f990,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f989,f55])).
% 0.22/0.52  fof(f989,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f839,f54])).
% 0.22/0.52  fof(f839,plain,(
% 0.22/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~spl5_10),
% 0.22/0.52    inference(resolution,[],[f144,f261])).
% 0.22/0.52  % (14600)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    ( ! [X4,X5] : (~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | v2_struct_0(X4) | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f260,f56])).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f259,f46])).
% 0.22/0.52  fof(f259,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f258,f44])).
% 0.22/0.52  fof(f258,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f257,f49])).
% 0.22/0.52  fof(f257,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f256,f47])).
% 0.22/0.52  fof(f256,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f255,f58])).
% 0.22/0.52  fof(f255,plain,(
% 0.22/0.52    ( ! [X4,X5] : (~l1_pre_topc(sK0) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f239,f57])).
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    ( ! [X4,X5] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v5_pre_topc(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),X4)) )),
% 0.22/0.52    inference(resolution,[],[f60,f132])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (~r4_tsep_1(X0,X2,X3) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f988,plain,(
% 0.22/0.52    spl5_5 | spl5_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f983,f107,f92])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    spl5_8 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.52  fof(f983,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f13,f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | spl5_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f107])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f972,plain,(
% 0.22/0.52    ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f971])).
% 0.22/0.52  fof(f971,plain,(
% 0.22/0.52    $false | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f970,f108])).
% 0.22/0.52  fof(f970,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f969,f53])).
% 0.22/0.52  fof(f969,plain,(
% 0.22/0.52    v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f968,f104])).
% 0.22/0.52  fof(f968,plain,(
% 0.22/0.52    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f967,f148])).
% 0.22/0.52  fof(f967,plain,(
% 0.22/0.52    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_9 | ~spl5_10 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f966,f84])).
% 0.22/0.52  fof(f966,plain,(
% 0.22/0.52    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_2 | ~spl5_5 | ~spl5_9 | ~spl5_10 | ~spl5_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f965,f152])).
% 0.22/0.52  fof(f965,plain,(
% 0.22/0.52    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_2 | ~spl5_5 | ~spl5_9 | ~spl5_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f964,f94])).
% 0.22/0.52  fof(f964,plain,(
% 0.22/0.52    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_2 | ~spl5_9 | ~spl5_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f963,f114])).
% 0.22/0.52  fof(f963,plain,(
% 0.22/0.52    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_2 | ~spl5_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f962,f79])).
% 0.22/0.52  fof(f962,plain,(
% 0.22/0.52    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f961,f52])).
% 0.22/0.52  fof(f961,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f960,f51])).
% 0.22/0.52  fof(f960,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f959,f50])).
% 0.22/0.52  fof(f959,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f958,f55])).
% 0.22/0.52  fof(f958,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | ~spl5_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f957,f54])).
% 0.22/0.52  fof(f957,plain,(
% 0.22/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | ~spl5_10),
% 0.22/0.52    inference(resolution,[],[f401,f144])).
% 0.22/0.52  fof(f401,plain,(
% 0.22/0.52    ( ! [X4,X5] : (~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | v2_struct_0(X4) | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f400,f56])).
% 0.22/0.52  fof(f400,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f399,f46])).
% 0.22/0.52  fof(f399,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f398,f44])).
% 0.22/0.52  fof(f398,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f397,f49])).
% 0.22/0.52  fof(f397,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f396,f47])).
% 0.22/0.52  fof(f396,plain,(
% 0.22/0.52    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f395,f58])).
% 0.22/0.52  fof(f395,plain,(
% 0.22/0.52    ( ! [X4,X5] : (~l1_pre_topc(sK0) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f379,f57])).
% 0.22/0.52  fof(f379,plain,(
% 0.22/0.52    ( ! [X4,X5] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | m1_subset_1(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))))) )),
% 0.22/0.52    inference(resolution,[],[f59,f132])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (~r4_tsep_1(X0,X2,X3) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f833,plain,(
% 0.22/0.52    spl5_10 | spl5_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f832,f107,f143])).
% 0.22/0.52  fof(f832,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f18,f108])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f831,plain,(
% 0.22/0.52    spl5_11 | spl5_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f830,f107,f147])).
% 0.22/0.52  fof(f830,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f16,f108])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f811,plain,(
% 0.22/0.52    spl5_2 | spl5_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f810,f107,f77])).
% 0.22/0.52  fof(f810,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f11,f108])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f799,plain,(
% 0.22/0.52    ~spl5_1 | spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_8),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f798])).
% 0.22/0.52  fof(f798,plain,(
% 0.22/0.52    $false | (~spl5_1 | spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f789,f78])).
% 0.22/0.52  fof(f789,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f788,f56])).
% 0.22/0.52  fof(f788,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f787,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~spl5_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f87])).
% 0.22/0.52  fof(f787,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_6 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f786,f99])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~spl5_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f97])).
% 0.22/0.52  fof(f786,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f785,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~spl5_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f73])).
% 0.22/0.52  fof(f785,plain,(
% 0.22/0.52    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f784,f52])).
% 0.22/0.52  fof(f784,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f783,f51])).
% 0.22/0.52  fof(f783,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f782,f50])).
% 0.22/0.52  fof(f782,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f781,f132])).
% 0.22/0.52  fof(f781,plain,(
% 0.22/0.52    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f780,f46])).
% 0.22/0.52  fof(f780,plain,(
% 0.22/0.52    ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f779,f44])).
% 0.22/0.52  fof(f779,plain,(
% 0.22/0.52    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f778,f49])).
% 0.22/0.52  fof(f778,plain,(
% 0.22/0.52    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f777,f47])).
% 0.22/0.52  fof(f777,plain,(
% 0.22/0.52    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f776,f55])).
% 0.22/0.52  fof(f776,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f775,f54])).
% 0.22/0.52  fof(f775,plain,(
% 0.22/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f774,f53])).
% 0.22/0.52  fof(f774,plain,(
% 0.22/0.52    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f773,f58])).
% 0.22/0.52  fof(f773,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f585,f57])).
% 0.22/0.52  fof(f585,plain,(
% 0.22/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(resolution,[],[f109,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | ~spl5_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f107])).
% 0.22/0.52  fof(f760,plain,(
% 0.22/0.52    ~spl5_1 | ~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_8),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f759])).
% 0.22/0.52  fof(f759,plain,(
% 0.22/0.52    $false | (~spl5_1 | ~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f758,f103])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | spl5_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f102])).
% 0.22/0.52  fof(f758,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f757,f56])).
% 0.22/0.52  fof(f757,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f756,f89])).
% 0.22/0.52  fof(f756,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_6 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f755,f99])).
% 0.22/0.52  fof(f755,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f754,f75])).
% 0.22/0.52  fof(f754,plain,(
% 0.22/0.52    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f753,f52])).
% 0.22/0.52  fof(f753,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f752,f51])).
% 0.22/0.52  fof(f752,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f751,f50])).
% 0.22/0.52  fof(f751,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f750,f132])).
% 0.22/0.52  fof(f750,plain,(
% 0.22/0.52    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f749,f46])).
% 0.22/0.52  fof(f749,plain,(
% 0.22/0.52    ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f748,f44])).
% 0.22/0.52  fof(f748,plain,(
% 0.22/0.52    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f747,f49])).
% 0.22/0.52  fof(f747,plain,(
% 0.22/0.52    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f746,f47])).
% 0.22/0.52  % (14592)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.52  fof(f746,plain,(
% 0.22/0.52    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f745,f55])).
% 0.22/0.52  fof(f745,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f744,f54])).
% 0.22/0.52  fof(f744,plain,(
% 0.22/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f743,f53])).
% 0.22/0.52  fof(f743,plain,(
% 0.22/0.52    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f742,f58])).
% 0.22/0.52  fof(f742,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f591,f57])).
% 0.22/0.52  fof(f591,plain,(
% 0.22/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(resolution,[],[f109,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f737,plain,(
% 0.22/0.52    ~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8 | spl5_11),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f736])).
% 0.22/0.52  fof(f736,plain,(
% 0.22/0.52    $false | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8 | spl5_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f735,f149])).
% 0.22/0.52  fof(f735,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f734,f56])).
% 0.22/0.52  fof(f734,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f733,f89])).
% 0.22/0.52  fof(f733,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_6 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f732,f99])).
% 0.22/0.52  fof(f732,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f731,f75])).
% 0.22/0.52  fof(f731,plain,(
% 0.22/0.52    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f730,f52])).
% 0.22/0.52  fof(f730,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f729,f51])).
% 0.22/0.52  fof(f729,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f728,f50])).
% 0.22/0.52  fof(f728,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f727,f132])).
% 0.22/0.52  fof(f727,plain,(
% 0.22/0.52    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f726,f46])).
% 0.22/0.52  fof(f726,plain,(
% 0.22/0.52    ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f725,f44])).
% 0.22/0.52  fof(f725,plain,(
% 0.22/0.52    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f724,f49])).
% 0.22/0.52  % (14596)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.52  fof(f724,plain,(
% 0.22/0.52    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f723,f47])).
% 0.22/0.52  fof(f723,plain,(
% 0.22/0.52    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f722,f55])).
% 0.22/0.52  fof(f722,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f721,f54])).
% 0.22/0.52  fof(f721,plain,(
% 0.22/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f720,f53])).
% 0.22/0.52  fof(f720,plain,(
% 0.22/0.52    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f719,f58])).
% 0.22/0.52  fof(f719,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(subsumption_resolution,[],[f590,f57])).
% 0.22/0.52  fof(f590,plain,(
% 0.22/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.52    inference(resolution,[],[f109,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f711,plain,(
% 0.22/0.52    ~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8 | spl5_10),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f710])).
% 0.22/0.52  fof(f710,plain,(
% 0.22/0.52    $false | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8 | spl5_10)),
% 0.22/0.52    inference(subsumption_resolution,[],[f667,f145])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | spl5_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f143])).
% 0.22/0.53  fof(f667,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f666,f56])).
% 0.22/0.53  fof(f666,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f665,f89])).
% 0.22/0.53  fof(f665,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_6 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f664,f99])).
% 0.22/0.53  fof(f664,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f663,f75])).
% 0.22/0.53  fof(f663,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f662,f52])).
% 0.22/0.53  fof(f662,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f661,f51])).
% 0.22/0.53  fof(f661,plain,(
% 0.22/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f660,f50])).
% 0.22/0.53  fof(f660,plain,(
% 0.22/0.53    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f659,f132])).
% 0.22/0.53  fof(f659,plain,(
% 0.22/0.53    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f658,f46])).
% 0.22/0.53  fof(f658,plain,(
% 0.22/0.53    ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f657,f44])).
% 0.22/0.53  fof(f657,plain,(
% 0.22/0.53    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f656,f49])).
% 0.22/0.53  fof(f656,plain,(
% 0.22/0.53    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f655,f47])).
% 0.22/0.53  fof(f655,plain,(
% 0.22/0.53    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f654,f55])).
% 0.22/0.53  fof(f654,plain,(
% 0.22/0.53    ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f653,f54])).
% 0.22/0.53  fof(f653,plain,(
% 0.22/0.53    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f652,f53])).
% 0.22/0.53  fof(f652,plain,(
% 0.22/0.53    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f651,f58])).
% 0.22/0.53  fof(f651,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f592,f57])).
% 0.22/0.53  fof(f592,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(resolution,[],[f109,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f669,plain,(
% 0.22/0.53    spl5_12 | ~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f644,f107,f97,f87,f73,f151])).
% 0.22/0.53  fof(f644,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f643,f56])).
% 0.22/0.53  fof(f643,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f642,f89])).
% 0.22/0.53  fof(f642,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_6 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f641,f99])).
% 0.22/0.53  fof(f641,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f605,f75])).
% 0.22/0.53  fof(f605,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f604,f52])).
% 0.22/0.53  fof(f604,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f603,f51])).
% 0.22/0.53  fof(f603,plain,(
% 0.22/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f602,f50])).
% 0.22/0.53  fof(f602,plain,(
% 0.22/0.53    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f601,f132])).
% 0.22/0.53  fof(f601,plain,(
% 0.22/0.53    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f600,f46])).
% 0.22/0.53  fof(f600,plain,(
% 0.22/0.53    ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f599,f44])).
% 0.22/0.53  fof(f599,plain,(
% 0.22/0.53    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f598,f49])).
% 0.22/0.53  fof(f598,plain,(
% 0.22/0.53    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f597,f47])).
% 0.22/0.53  fof(f597,plain,(
% 0.22/0.53    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f596,f55])).
% 0.22/0.53  fof(f596,plain,(
% 0.22/0.53    ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f595,f54])).
% 0.22/0.53  fof(f595,plain,(
% 0.22/0.53    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f594,f53])).
% 0.22/0.53  fof(f594,plain,(
% 0.22/0.53    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f593,f58])).
% 0.22/0.53  fof(f593,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f588,f57])).
% 0.22/0.53  fof(f588,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(resolution,[],[f109,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f668,plain,(
% 0.22/0.53    spl5_5 | ~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f628,f107,f97,f87,f73,f92])).
% 0.22/0.53  fof(f628,plain,(
% 0.22/0.53    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f627,f56])).
% 0.22/0.53  fof(f627,plain,(
% 0.22/0.53    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f626,f89])).
% 0.22/0.53  fof(f626,plain,(
% 0.22/0.53    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_6 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f625,f99])).
% 0.22/0.53  fof(f625,plain,(
% 0.22/0.53    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f624,f75])).
% 0.22/0.53  fof(f624,plain,(
% 0.22/0.53    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f623,f52])).
% 0.22/0.53  fof(f623,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f622,f51])).
% 0.22/0.53  fof(f622,plain,(
% 0.22/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f621,f50])).
% 0.22/0.53  fof(f621,plain,(
% 0.22/0.53    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f620,f132])).
% 0.22/0.53  fof(f620,plain,(
% 0.22/0.53    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f619,f46])).
% 0.22/0.53  fof(f619,plain,(
% 0.22/0.53    ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f618,f44])).
% 0.22/0.53  fof(f618,plain,(
% 0.22/0.53    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f617,f49])).
% 0.22/0.53  fof(f617,plain,(
% 0.22/0.53    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f616,f47])).
% 0.22/0.53  fof(f616,plain,(
% 0.22/0.53    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f615,f55])).
% 0.22/0.53  fof(f615,plain,(
% 0.22/0.53    ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f614,f54])).
% 0.22/0.53  % (14611)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.22/0.53  fof(f614,plain,(
% 0.22/0.53    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f613,f53])).
% 0.22/0.53  fof(f613,plain,(
% 0.22/0.53    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f612,f58])).
% 0.22/0.53  fof(f612,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f587,f57])).
% 0.22/0.53  fof(f587,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(resolution,[],[f109,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f584,plain,(
% 0.22/0.53    spl5_8 | spl5_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f583,f151,f107])).
% 0.22/0.53  fof(f583,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | spl5_12),
% 0.22/0.53    inference(subsumption_resolution,[],[f14,f153])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl5_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f151])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f556,plain,(
% 0.22/0.53    spl5_8 | spl5_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f555,f82,f107])).
% 0.22/0.53  fof(f555,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | spl5_3),
% 0.22/0.53    inference(subsumption_resolution,[],[f15,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | spl5_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f82])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f554,plain,(
% 0.22/0.53    ~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_8),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f553])).
% 0.22/0.53  fof(f553,plain,(
% 0.22/0.53    $false | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f552,f99])).
% 0.22/0.53  fof(f552,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f551,f83])).
% 0.22/0.53  fof(f551,plain,(
% 0.22/0.53    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | (~spl5_1 | ~spl5_4 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f550,f56])).
% 0.22/0.53  fof(f550,plain,(
% 0.22/0.53    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_4 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f549,f89])).
% 0.22/0.53  fof(f549,plain,(
% 0.22/0.53    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f548,f75])).
% 0.22/0.53  fof(f548,plain,(
% 0.22/0.53    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f547,f52])).
% 0.22/0.53  fof(f547,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f546,f51])).
% 0.22/0.53  fof(f546,plain,(
% 0.22/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f545,f50])).
% 0.22/0.53  fof(f545,plain,(
% 0.22/0.53    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f544,f132])).
% 0.22/0.53  fof(f544,plain,(
% 0.22/0.53    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f543,f46])).
% 0.22/0.53  fof(f543,plain,(
% 0.22/0.53    ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f542,f44])).
% 0.22/0.53  fof(f542,plain,(
% 0.22/0.53    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f541,f49])).
% 0.22/0.53  fof(f541,plain,(
% 0.22/0.53    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f540,f47])).
% 0.22/0.53  fof(f540,plain,(
% 0.22/0.53    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f539,f55])).
% 0.22/0.53  fof(f539,plain,(
% 0.22/0.53    ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f538,f54])).
% 0.22/0.53  fof(f538,plain,(
% 0.22/0.53    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f537,f53])).
% 0.22/0.53  fof(f537,plain,(
% 0.22/0.53    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f536,f58])).
% 0.22/0.53  fof(f536,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f156,f57])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(resolution,[],[f67,f109])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f527,plain,(
% 0.22/0.53    spl5_3 | spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f526,f97,f82])).
% 0.22/0.53  fof(f526,plain,(
% 0.22/0.53    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | spl5_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f31,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | spl5_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f97])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f488,plain,(
% 0.22/0.53    ~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f487])).
% 0.22/0.53  fof(f487,plain,(
% 0.22/0.53    $false | (~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f486,f98])).
% 0.22/0.53  fof(f486,plain,(
% 0.22/0.53    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f485,f53])).
% 0.22/0.53  fof(f485,plain,(
% 0.22/0.53    v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f484,f104])).
% 0.22/0.53  fof(f484,plain,(
% 0.22/0.53    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f483,f148])).
% 0.22/0.53  fof(f483,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_9 | ~spl5_10 | ~spl5_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f482,f84])).
% 0.22/0.53  fof(f482,plain,(
% 0.22/0.53    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_5 | ~spl5_9 | ~spl5_10 | ~spl5_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f481,f152])).
% 0.22/0.53  fof(f481,plain,(
% 0.22/0.53    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_5 | ~spl5_9 | ~spl5_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f480,f94])).
% 0.22/0.53  fof(f480,plain,(
% 0.22/0.53    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_9 | ~spl5_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f479,f114])).
% 0.22/0.53  fof(f479,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f478,f79])).
% 0.22/0.53  fof(f478,plain,(
% 0.22/0.53    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~spl5_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f477,f52])).
% 0.22/0.53  fof(f477,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~spl5_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f476,f51])).
% 0.22/0.53  fof(f476,plain,(
% 0.22/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~spl5_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f475,f50])).
% 0.22/0.53  fof(f475,plain,(
% 0.22/0.53    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~spl5_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f474,f55])).
% 0.22/0.53  fof(f474,plain,(
% 0.22/0.53    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~spl5_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f473,f54])).
% 0.22/0.53  fof(f473,plain,(
% 0.22/0.53    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v2_struct_0(sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~spl5_10),
% 0.22/0.53    inference(resolution,[],[f335,f144])).
% 0.22/0.53  % (14599)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.53  fof(f335,plain,(
% 0.22/0.53    ( ! [X4,X5] : (~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | v2_struct_0(X4) | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f334,f56])).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f333,f46])).
% 0.22/0.53  fof(f333,plain,(
% 0.22/0.53    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f332,f44])).
% 0.22/0.53  fof(f332,plain,(
% 0.22/0.53    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f331,f49])).
% 0.22/0.53  fof(f331,plain,(
% 0.22/0.53    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f330,f47])).
% 0.22/0.53  fof(f330,plain,(
% 0.22/0.53    ( ! [X4,X5] : (v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f329,f58])).
% 0.22/0.53  fof(f329,plain,(
% 0.22/0.53    ( ! [X4,X5] : (~l1_pre_topc(sK0) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f313,f57])).
% 0.22/0.53  fof(f313,plain,(
% 0.22/0.53    ( ! [X4,X5] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK3),u1_struct_0(sK3),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK3),sK3,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_1(k2_tmap_1(sK0,X4,X5,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,X4,X5,sK4),u1_struct_0(sK4),u1_struct_0(X4)) | ~v5_pre_topc(k2_tmap_1(sK0,X4,X5,sK4),sK4,X4) | ~m1_subset_1(k2_tmap_1(sK0,X4,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X4)))) | v1_funct_2(k2_tmap_1(sK0,X4,X5,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X4))) )),
% 0.22/0.53    inference(resolution,[],[f61,f132])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~r4_tsep_1(X0,X2,X3) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    spl5_10 | spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f192,f97,f143])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | spl5_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f34,f98])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    spl5_12 | spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f190,f97,f151])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl5_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f30,f98])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    spl5_11 | spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f188,f97,f147])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | spl5_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f32,f98])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    spl5_6 | spl5_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f181,f112,f97])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | spl5_9),
% 0.22/0.53    inference(subsumption_resolution,[],[f28,f113])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8 | spl5_9),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    $false | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8 | spl5_9)),
% 0.22/0.53    inference(subsumption_resolution,[],[f176,f56])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    v2_struct_0(sK0) | (~spl5_1 | ~spl5_4 | ~spl5_6 | ~spl5_8 | spl5_9)),
% 0.22/0.53    inference(subsumption_resolution,[],[f175,f89])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_6 | ~spl5_8 | spl5_9)),
% 0.22/0.53    inference(subsumption_resolution,[],[f174,f99])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_8 | spl5_9)),
% 0.22/0.53    inference(subsumption_resolution,[],[f173,f75])).
% 0.22/0.53  % (14604)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | (~spl5_8 | spl5_9)),
% 0.22/0.53    inference(subsumption_resolution,[],[f172,f113])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f171,f52])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f170,f51])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f169,f50])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f168,f132])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f167,f46])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f166,f44])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f165,f49])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f164,f47])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f163,f55])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f162,f54])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f161,f53])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f160,f58])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f159,f57])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | v2_struct_0(sK0) | ~spl5_8),
% 0.22/0.53    inference(resolution,[],[f64,f109])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_9 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f141,f107,f102,f97,f92,f87,f82,f77,f73,f112,f151,f147,f143])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f140,f109])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f139,f89])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f138,f99])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f137,f75])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f136,f104])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f135,f84])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | (~spl5_2 | ~spl5_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f134,f94])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) | ~spl5_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f43,f79])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    spl5_8 | spl5_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f12,f112,f107])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl5_8 | spl5_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f17,f102,f107])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl5_6 | spl5_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f102,f97])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  % (14590)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    spl5_6 | spl5_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f92,f97])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl5_4 | spl5_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f21,f92,f87])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    spl5_4 | spl5_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f23,f82,f87])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    spl5_1 | spl5_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f82,f73])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    spl5_1 | spl5_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f77,f73])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (14595)------------------------------
% 0.22/0.53  % (14595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14595)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (14595)Memory used [KB]: 6012
% 0.22/0.53  % (14595)Time elapsed: 0.043 s
% 0.22/0.53  % (14595)------------------------------
% 0.22/0.53  % (14595)------------------------------
% 0.22/0.53  % (14585)Success in time 0.169 s
%------------------------------------------------------------------------------
