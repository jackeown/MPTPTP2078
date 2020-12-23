%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 282 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :   19
%              Number of atoms          :  469 (2186 expanded)
%              Number of equality atoms :   23 ( 293 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f104,f116,f141,f146,f184])).

fof(f184,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f182,f61])).

fof(f61,plain,(
    ~ r2_hidden(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f51,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f51,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | sK3 != X5 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
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
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => X3 != X5 ) ) ) ) ) ) ),
    inference(rectify,[],[f10])).

fof(f10,negated_conjecture,(
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
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X1))
                           => X3 != X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ~ ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X2))
                         => X3 != X4 )
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => X3 != X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tmap_1)).

fof(f182,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f181,f62])).

fof(f62,plain,(
    ~ r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f52,f40])).

fof(f52,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f181,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(resolution,[],[f179,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f179,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f178,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f178,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f177,f82])).

fof(f82,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_3
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f177,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f176,f86])).

fof(f86,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_4
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f176,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f175,f90])).

fof(f90,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_5
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f175,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f174,f29])).

fof(f29,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f174,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f173,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f173,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f172,f31])).

fof(f31,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f172,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f171,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f171,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f170,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f170,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(superposition,[],[f68,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f68,plain,
    ( r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_1
  <=> r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f146,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5 ),
    inference(subsumption_resolution,[],[f144,f108])).

fof(f108,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_2
    | spl5_5 ),
    inference(resolution,[],[f107,f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f107,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_2
    | spl5_5 ),
    inference(subsumption_resolution,[],[f105,f90])).

fof(f105,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f72,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f72,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_2
  <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f144,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f143,f34])).

fof(f143,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f82,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f141,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f139,f32])).

fof(f139,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f138,f29])).

fof(f138,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f137,f28])).

fof(f137,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f136,f31])).

fof(f136,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f135,f30])).

fof(f135,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f134,f34])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f91,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f91,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f116,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f114,f32])).

fof(f114,plain,
    ( v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f113,f29])).

fof(f113,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f112,f28])).

fof(f112,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f111,f31])).

fof(f111,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f110,f30])).

fof(f110,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f109,f34])).

fof(f109,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(resolution,[],[f83,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f104,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f102,f32])).

fof(f102,plain,
    ( v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f101,f29])).

fof(f101,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f100,f28])).

fof(f100,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f99,f31])).

fof(f99,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f98,f30])).

fof(f98,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f97,f34])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(resolution,[],[f87,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f73,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f63,f70,f66])).

fof(f63,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(resolution,[],[f27,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f27,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:17:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.43  % (1170)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.47  % (1155)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.47  % (1165)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.48  % (1166)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.48  % (1167)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.49  % (1156)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (1172)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.49  % (1156)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f185,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f73,f104,f116,f141,f146,f184])).
% 0.19/0.49  fof(f184,plain,(
% 0.19/0.49    ~spl5_1 | ~spl5_3 | ~spl5_4 | spl5_5),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f183])).
% 0.19/0.49  fof(f183,plain,(
% 0.19/0.49    $false | (~spl5_1 | ~spl5_3 | ~spl5_4 | spl5_5)),
% 0.19/0.49    inference(subsumption_resolution,[],[f182,f61])).
% 0.19/0.49  fof(f61,plain,(
% 0.19/0.49    ~r2_hidden(sK3,u1_struct_0(sK1))),
% 0.19/0.49    inference(resolution,[],[f51,f40])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.19/0.49    inference(equality_resolution,[],[f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK1)) | sK3 != X5) )),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 0.19/0.49    inference(rectify,[],[f10])).
% 0.19/0.49  fof(f10,negated_conjecture,(
% 0.19/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 0.19/0.49    inference(negated_conjecture,[],[f9])).
% 0.19/0.49  fof(f9,conjecture,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tmap_1)).
% 0.19/0.49  fof(f182,plain,(
% 0.19/0.49    r2_hidden(sK3,u1_struct_0(sK1)) | (~spl5_1 | ~spl5_3 | ~spl5_4 | spl5_5)),
% 0.19/0.49    inference(subsumption_resolution,[],[f181,f62])).
% 0.19/0.49  fof(f62,plain,(
% 0.19/0.49    ~r2_hidden(sK3,u1_struct_0(sK2))),
% 0.19/0.49    inference(resolution,[],[f52,f40])).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.19/0.49    inference(equality_resolution,[],[f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X4) )),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f181,plain,(
% 0.19/0.49    r2_hidden(sK3,u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK1)) | (~spl5_1 | ~spl5_3 | ~spl5_4 | spl5_5)),
% 0.19/0.49    inference(resolution,[],[f179,f56])).
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f48])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.19/0.49    inference(cnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.19/0.49  fof(f179,plain,(
% 0.19/0.49    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl5_1 | ~spl5_3 | ~spl5_4 | spl5_5)),
% 0.19/0.49    inference(subsumption_resolution,[],[f178,f32])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ~v2_struct_0(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f178,plain,(
% 0.19/0.49    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_3 | ~spl5_4 | spl5_5)),
% 0.19/0.49    inference(subsumption_resolution,[],[f177,f82])).
% 0.19/0.49  fof(f82,plain,(
% 0.19/0.49    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | ~spl5_3),
% 0.19/0.49    inference(avatar_component_clause,[],[f81])).
% 0.19/0.49  fof(f81,plain,(
% 0.19/0.49    spl5_3 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.49  fof(f177,plain,(
% 0.19/0.49    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_4 | spl5_5)),
% 0.19/0.49    inference(subsumption_resolution,[],[f176,f86])).
% 0.19/0.49  fof(f86,plain,(
% 0.19/0.49    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_4),
% 0.19/0.49    inference(avatar_component_clause,[],[f85])).
% 0.19/0.49  fof(f85,plain,(
% 0.19/0.49    spl5_4 <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.49  fof(f176,plain,(
% 0.19/0.49    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | (~spl5_1 | spl5_5)),
% 0.19/0.49    inference(subsumption_resolution,[],[f175,f90])).
% 0.19/0.49  fof(f90,plain,(
% 0.19/0.49    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | spl5_5),
% 0.19/0.49    inference(avatar_component_clause,[],[f89])).
% 0.19/0.49  fof(f89,plain,(
% 0.19/0.49    spl5_5 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.49  fof(f175,plain,(
% 0.19/0.49    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.19/0.49    inference(subsumption_resolution,[],[f174,f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    m1_pre_topc(sK2,sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f174,plain,(
% 0.19/0.49    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.19/0.49    inference(subsumption_resolution,[],[f173,f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ~v2_struct_0(sK2)),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f173,plain,(
% 0.19/0.49    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.19/0.49    inference(subsumption_resolution,[],[f172,f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    m1_pre_topc(sK1,sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f172,plain,(
% 0.19/0.49    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.19/0.49    inference(subsumption_resolution,[],[f171,f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ~v2_struct_0(sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f171,plain,(
% 0.19/0.49    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.19/0.49    inference(subsumption_resolution,[],[f170,f34])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    l1_pre_topc(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f170,plain,(
% 0.19/0.49    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.19/0.49    inference(superposition,[],[f68,f53])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f39])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3) )),
% 0.19/0.49    inference(cnf_transformation,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).
% 0.19/0.49  fof(f68,plain,(
% 0.19/0.49    r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl5_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f66])).
% 0.19/0.49  fof(f66,plain,(
% 0.19/0.49    spl5_1 <=> r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.49  fof(f146,plain,(
% 0.19/0.49    ~spl5_2 | ~spl5_3 | spl5_5),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f145])).
% 0.19/0.49  fof(f145,plain,(
% 0.19/0.49    $false | (~spl5_2 | ~spl5_3 | spl5_5)),
% 0.19/0.49    inference(subsumption_resolution,[],[f144,f108])).
% 0.19/0.49  fof(f108,plain,(
% 0.19/0.49    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | (~spl5_2 | spl5_5)),
% 0.19/0.49    inference(resolution,[],[f107,f35])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.49  fof(f107,plain,(
% 0.19/0.49    ~l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | (~spl5_2 | spl5_5)),
% 0.19/0.49    inference(subsumption_resolution,[],[f105,f90])).
% 0.19/0.49  fof(f105,plain,(
% 0.19/0.49    ~l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_2),
% 0.19/0.49    inference(resolution,[],[f72,f37])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.19/0.49  fof(f72,plain,(
% 0.19/0.49    v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl5_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f70])).
% 0.19/0.49  fof(f70,plain,(
% 0.19/0.49    spl5_2 <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.49  fof(f144,plain,(
% 0.19/0.49    l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_3),
% 0.19/0.49    inference(subsumption_resolution,[],[f143,f34])).
% 0.19/0.49  fof(f143,plain,(
% 0.19/0.49    ~l1_pre_topc(sK0) | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_3),
% 0.19/0.49    inference(resolution,[],[f82,f36])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.19/0.49  fof(f141,plain,(
% 0.19/0.49    ~spl5_5),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f140])).
% 0.19/0.49  fof(f140,plain,(
% 0.19/0.49    $false | ~spl5_5),
% 0.19/0.49    inference(subsumption_resolution,[],[f139,f32])).
% 0.19/0.49  fof(f139,plain,(
% 0.19/0.49    v2_struct_0(sK0) | ~spl5_5),
% 0.19/0.49    inference(subsumption_resolution,[],[f138,f29])).
% 0.19/0.49  fof(f138,plain,(
% 0.19/0.49    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_5),
% 0.19/0.49    inference(subsumption_resolution,[],[f137,f28])).
% 0.19/0.49  fof(f137,plain,(
% 0.19/0.49    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_5),
% 0.19/0.49    inference(subsumption_resolution,[],[f136,f31])).
% 0.19/0.49  fof(f136,plain,(
% 0.19/0.49    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_5),
% 0.19/0.49    inference(subsumption_resolution,[],[f135,f30])).
% 0.19/0.49  fof(f135,plain,(
% 0.19/0.49    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_5),
% 0.19/0.49    inference(subsumption_resolution,[],[f134,f34])).
% 0.19/0.49  fof(f134,plain,(
% 0.19/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_5),
% 0.19/0.49    inference(resolution,[],[f91,f42])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.19/0.49  fof(f91,plain,(
% 0.19/0.49    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_5),
% 0.19/0.49    inference(avatar_component_clause,[],[f89])).
% 0.19/0.49  fof(f116,plain,(
% 0.19/0.49    spl5_3),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f115])).
% 0.19/0.49  fof(f115,plain,(
% 0.19/0.49    $false | spl5_3),
% 0.19/0.49    inference(subsumption_resolution,[],[f114,f32])).
% 0.19/0.49  fof(f114,plain,(
% 0.19/0.49    v2_struct_0(sK0) | spl5_3),
% 0.19/0.49    inference(subsumption_resolution,[],[f113,f29])).
% 0.19/0.49  fof(f113,plain,(
% 0.19/0.49    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_3),
% 0.19/0.49    inference(subsumption_resolution,[],[f112,f28])).
% 0.19/0.49  fof(f112,plain,(
% 0.19/0.49    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_3),
% 0.19/0.49    inference(subsumption_resolution,[],[f111,f31])).
% 0.19/0.49  fof(f111,plain,(
% 0.19/0.49    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_3),
% 0.19/0.49    inference(subsumption_resolution,[],[f110,f30])).
% 0.19/0.49  fof(f110,plain,(
% 0.19/0.49    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_3),
% 0.19/0.49    inference(subsumption_resolution,[],[f109,f34])).
% 0.19/0.49  fof(f109,plain,(
% 0.19/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_3),
% 0.19/0.49    inference(resolution,[],[f83,f44])).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f24])).
% 0.19/0.49  fof(f83,plain,(
% 0.19/0.49    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | spl5_3),
% 0.19/0.49    inference(avatar_component_clause,[],[f81])).
% 0.19/0.49  fof(f104,plain,(
% 0.19/0.49    spl5_4),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f103])).
% 0.19/0.49  fof(f103,plain,(
% 0.19/0.49    $false | spl5_4),
% 0.19/0.49    inference(subsumption_resolution,[],[f102,f32])).
% 0.19/0.49  fof(f102,plain,(
% 0.19/0.49    v2_struct_0(sK0) | spl5_4),
% 0.19/0.49    inference(subsumption_resolution,[],[f101,f29])).
% 0.19/0.49  fof(f101,plain,(
% 0.19/0.49    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_4),
% 0.19/0.49    inference(subsumption_resolution,[],[f100,f28])).
% 0.19/0.49  fof(f100,plain,(
% 0.19/0.49    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_4),
% 0.19/0.49    inference(subsumption_resolution,[],[f99,f31])).
% 0.19/0.49  fof(f99,plain,(
% 0.19/0.49    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_4),
% 0.19/0.49    inference(subsumption_resolution,[],[f98,f30])).
% 0.19/0.49  fof(f98,plain,(
% 0.19/0.49    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_4),
% 0.19/0.49    inference(subsumption_resolution,[],[f97,f34])).
% 0.19/0.49  fof(f97,plain,(
% 0.19/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_4),
% 0.19/0.49    inference(resolution,[],[f87,f43])).
% 0.19/0.49  fof(f43,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f24])).
% 0.19/0.49  fof(f87,plain,(
% 0.19/0.49    ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | spl5_4),
% 0.19/0.49    inference(avatar_component_clause,[],[f85])).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    spl5_1 | spl5_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f63,f70,f66])).
% 0.19/0.49  fof(f63,plain,(
% 0.19/0.49    v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.19/0.49    inference(resolution,[],[f27,f41])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.49    inference(flattening,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (1156)------------------------------
% 0.19/0.49  % (1156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (1156)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (1156)Memory used [KB]: 10618
% 0.19/0.49  % (1156)Time elapsed: 0.082 s
% 0.19/0.49  % (1156)------------------------------
% 0.19/0.49  % (1156)------------------------------
% 0.19/0.49  % (1177)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.49  % (1158)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.49  % (1154)Success in time 0.141 s
%------------------------------------------------------------------------------
