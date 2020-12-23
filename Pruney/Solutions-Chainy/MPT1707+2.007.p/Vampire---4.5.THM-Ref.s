%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:47 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 496 expanded)
%              Number of leaves         :   14 (  91 expanded)
%              Depth                    :   23
%              Number of atoms          :  704 (4021 expanded)
%              Number of equality atoms :   23 ( 545 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f102,f111,f131,f147,f163,f187,f214])).

fof(f214,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f212,f52])).

fof(f52,plain,(
    ~ r2_hidden(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f46,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f46,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | sK3 != X5 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f212,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f211,f64])).

fof(f64,plain,(
    ~ r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f47,f36])).

fof(f47,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f211,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | spl5_8 ),
    inference(resolution,[],[f209,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
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

fof(f209,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f143,f208])).

fof(f208,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | spl5_8 ),
    inference(subsumption_resolution,[],[f207,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f207,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | spl5_8 ),
    inference(subsumption_resolution,[],[f206,f80])).

fof(f80,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_3
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f206,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | spl5_5
    | spl5_8 ),
    inference(subsumption_resolution,[],[f205,f84])).

fof(f84,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_4
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f205,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_5
    | spl5_8 ),
    inference(subsumption_resolution,[],[f204,f88])).

fof(f88,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_5
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f204,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f203,f23])).

fof(f23,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f203,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f202,f22])).

fof(f22,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f202,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f201,f25])).

fof(f25,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f201,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f200,f24])).

fof(f24,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f200,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f188,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f188,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(superposition,[],[f151,f48])).

fof(f48,plain,(
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
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f151,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl5_8
  <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f143,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_6 ),
    inference(resolution,[],[f93,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f93,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f187,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_8
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_8
    | spl5_10 ),
    inference(subsumption_resolution,[],[f185,f162])).

fof(f162,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl5_10
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f185,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f184,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(f184,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f183,f26])).

fof(f183,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f182,f80])).

fof(f182,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f181,f84])).

fof(f181,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f180,f88])).

fof(f180,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f179,f23])).

fof(f179,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f178,f22])).

fof(f178,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f177,f25])).

fof(f177,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f176,f24])).

fof(f176,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f164,f28])).

fof(f164,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(superposition,[],[f152,f48])).

fof(f152,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f150])).

fof(f163,plain,
    ( ~ spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f65,f60,f160])).

fof(f60,plain,
    ( spl5_2
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f65,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f47,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f147,plain,
    ( spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f145,f52])).

fof(f145,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f144,f64])).

fof(f144,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK1))
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(resolution,[],[f141,f51])).

fof(f141,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f140,f26])).

fof(f140,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK0)
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f139,f80])).

fof(f139,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_2
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f138,f84])).

fof(f138,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_2
    | spl5_5 ),
    inference(subsumption_resolution,[],[f137,f88])).

fof(f137,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f136,f23])).

fof(f136,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f135,f22])).

fof(f135,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f134,f25])).

fof(f134,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f133,f24])).

fof(f133,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f132,f28])).

fof(f132,plain,
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
    | spl5_2 ),
    inference(superposition,[],[f71,f48])).

fof(f71,plain,
    ( r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f68,f70])).

fof(f70,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f67,f62])).

fof(f62,plain,
    ( ~ v1_xboole_0(sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f67,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(resolution,[],[f21,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

% (9436)Refutation not found, incomplete strategy% (9436)------------------------------
% (9436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f21,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f11])).

% (9436)Termination reason: Refutation not found, incomplete strategy

fof(f68,plain,
    ( r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(resolution,[],[f21,f34])).

fof(f131,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f130])).

% (9436)Memory used [KB]: 10618
% (9436)Time elapsed: 0.107 s
fof(f130,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f129,f26])).

% (9436)------------------------------
% (9436)------------------------------
fof(f129,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f128,f23])).

fof(f128,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f127,f22])).

fof(f127,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f126,f25])).

fof(f126,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f125,f24])).

fof(f125,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f124,f28])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f89,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f89,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f111,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f109,f26])).

fof(f109,plain,
    ( v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f108,f23])).

fof(f108,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f107,f22])).

fof(f107,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f106,f25])).

fof(f106,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f105,f24])).

fof(f105,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f104,f28])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(resolution,[],[f81,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f102,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f100,f26])).

fof(f100,plain,
    ( v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f99,f23])).

fof(f99,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f98,f22])).

fof(f98,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f97,f25])).

fof(f97,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f96,f24])).

fof(f96,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f95,f28])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(resolution,[],[f85,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f94,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f77,f91,f87,f83,f79])).

fof(f77,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f76,f26])).

fof(f76,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f75,f23])).

fof(f75,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f74,f22])).

fof(f74,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f73,f25])).

fof(f73,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f72,f24])).

fof(f72,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f69,f28])).

fof(f69,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f21,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:03:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.48  % (9428)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (9429)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (9421)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (9420)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (9427)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (9418)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (9430)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (9419)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (9433)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (9431)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (9415)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (9423)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.29/0.53  % (9425)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.29/0.53  % (9417)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.29/0.53  % (9426)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.29/0.53  % (9416)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.53  % (9436)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.29/0.53  % (9416)Refutation found. Thanks to Tanya!
% 1.29/0.53  % SZS status Theorem for theBenchmark
% 1.29/0.53  % SZS output start Proof for theBenchmark
% 1.29/0.53  fof(f215,plain,(
% 1.29/0.53    $false),
% 1.29/0.53    inference(avatar_sat_refutation,[],[f94,f102,f111,f131,f147,f163,f187,f214])).
% 1.29/0.53  fof(f214,plain,(
% 1.29/0.53    ~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_6 | spl5_8),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f213])).
% 1.29/0.53  fof(f213,plain,(
% 1.29/0.53    $false | (~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_6 | spl5_8)),
% 1.29/0.53    inference(subsumption_resolution,[],[f212,f52])).
% 1.29/0.53  fof(f52,plain,(
% 1.29/0.53    ~r2_hidden(sK3,u1_struct_0(sK1))),
% 1.29/0.53    inference(resolution,[],[f46,f36])).
% 1.29/0.53  fof(f36,plain,(
% 1.29/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f16])).
% 1.29/0.53  fof(f16,plain,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.29/0.53    inference(ennf_transformation,[],[f4])).
% 1.29/0.53  fof(f4,axiom,(
% 1.29/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.29/0.53  fof(f46,plain,(
% 1.29/0.53    ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.29/0.53    inference(equality_resolution,[],[f20])).
% 1.29/0.53  fof(f20,plain,(
% 1.29/0.53    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK1)) | sK3 != X5) )),
% 1.29/0.53    inference(cnf_transformation,[],[f11])).
% 1.29/0.53  fof(f11,plain,(
% 1.29/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.29/0.53    inference(flattening,[],[f10])).
% 1.29/0.53  fof(f10,plain,(
% 1.29/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f9])).
% 1.29/0.53  fof(f9,plain,(
% 1.29/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 1.29/0.53    inference(rectify,[],[f8])).
% 1.29/0.53  fof(f8,negated_conjecture,(
% 1.29/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 1.29/0.53    inference(negated_conjecture,[],[f7])).
% 1.29/0.53  fof(f7,conjecture,(
% 1.29/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tmap_1)).
% 1.29/0.53  fof(f212,plain,(
% 1.29/0.53    r2_hidden(sK3,u1_struct_0(sK1)) | (~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_6 | spl5_8)),
% 1.29/0.53    inference(subsumption_resolution,[],[f211,f64])).
% 1.29/0.53  fof(f64,plain,(
% 1.29/0.53    ~r2_hidden(sK3,u1_struct_0(sK2))),
% 1.29/0.53    inference(resolution,[],[f47,f36])).
% 1.29/0.53  fof(f47,plain,(
% 1.29/0.53    ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.29/0.53    inference(equality_resolution,[],[f19])).
% 1.29/0.53  fof(f19,plain,(
% 1.29/0.53    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X4) )),
% 1.29/0.53    inference(cnf_transformation,[],[f11])).
% 1.29/0.53  fof(f211,plain,(
% 1.29/0.53    r2_hidden(sK3,u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK1)) | (~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_6 | spl5_8)),
% 1.29/0.53    inference(resolution,[],[f209,f51])).
% 1.29/0.53  fof(f51,plain,(
% 1.29/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 1.29/0.53    inference(equality_resolution,[],[f43])).
% 1.29/0.53  fof(f43,plain,(
% 1.29/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.29/0.53    inference(cnf_transformation,[],[f1])).
% 1.29/0.53  fof(f1,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.29/0.53  fof(f209,plain,(
% 1.29/0.53    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_6 | spl5_8)),
% 1.29/0.53    inference(subsumption_resolution,[],[f143,f208])).
% 1.29/0.53  fof(f208,plain,(
% 1.29/0.53    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl5_3 | ~spl5_4 | spl5_5 | spl5_8)),
% 1.29/0.53    inference(subsumption_resolution,[],[f207,f26])).
% 1.29/0.53  fof(f26,plain,(
% 1.29/0.53    ~v2_struct_0(sK0)),
% 1.29/0.53    inference(cnf_transformation,[],[f11])).
% 1.29/0.53  fof(f207,plain,(
% 1.29/0.53    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | spl5_5 | spl5_8)),
% 1.29/0.53    inference(subsumption_resolution,[],[f206,f80])).
% 1.29/0.53  fof(f80,plain,(
% 1.29/0.53    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | ~spl5_3),
% 1.29/0.53    inference(avatar_component_clause,[],[f79])).
% 1.29/0.53  fof(f79,plain,(
% 1.29/0.53    spl5_3 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.29/0.53  fof(f206,plain,(
% 1.29/0.53    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | (~spl5_4 | spl5_5 | spl5_8)),
% 1.29/0.53    inference(subsumption_resolution,[],[f205,f84])).
% 1.29/0.53  fof(f84,plain,(
% 1.29/0.53    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_4),
% 1.29/0.53    inference(avatar_component_clause,[],[f83])).
% 1.29/0.53  fof(f83,plain,(
% 1.29/0.53    spl5_4 <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.29/0.53  fof(f205,plain,(
% 1.29/0.53    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | (spl5_5 | spl5_8)),
% 1.29/0.53    inference(subsumption_resolution,[],[f204,f88])).
% 1.29/0.53  fof(f88,plain,(
% 1.29/0.53    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | spl5_5),
% 1.29/0.53    inference(avatar_component_clause,[],[f87])).
% 1.29/0.53  fof(f87,plain,(
% 1.29/0.53    spl5_5 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.29/0.53  fof(f204,plain,(
% 1.29/0.53    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_8),
% 1.29/0.53    inference(subsumption_resolution,[],[f203,f23])).
% 1.29/0.53  fof(f23,plain,(
% 1.29/0.53    m1_pre_topc(sK2,sK0)),
% 1.29/0.53    inference(cnf_transformation,[],[f11])).
% 1.29/0.53  fof(f203,plain,(
% 1.29/0.53    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_8),
% 1.29/0.53    inference(subsumption_resolution,[],[f202,f22])).
% 1.29/0.53  fof(f22,plain,(
% 1.29/0.53    ~v2_struct_0(sK2)),
% 1.29/0.53    inference(cnf_transformation,[],[f11])).
% 1.29/0.53  fof(f202,plain,(
% 1.29/0.53    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_8),
% 1.29/0.53    inference(subsumption_resolution,[],[f201,f25])).
% 1.29/0.53  fof(f25,plain,(
% 1.29/0.53    m1_pre_topc(sK1,sK0)),
% 1.29/0.53    inference(cnf_transformation,[],[f11])).
% 1.29/0.53  fof(f201,plain,(
% 1.29/0.53    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_8),
% 1.29/0.53    inference(subsumption_resolution,[],[f200,f24])).
% 1.29/0.53  fof(f24,plain,(
% 1.29/0.53    ~v2_struct_0(sK1)),
% 1.29/0.53    inference(cnf_transformation,[],[f11])).
% 1.29/0.53  fof(f200,plain,(
% 1.29/0.53    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_8),
% 1.29/0.53    inference(subsumption_resolution,[],[f188,f28])).
% 1.29/0.53  fof(f28,plain,(
% 1.29/0.53    l1_pre_topc(sK0)),
% 1.29/0.53    inference(cnf_transformation,[],[f11])).
% 1.29/0.53  fof(f188,plain,(
% 1.29/0.53    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_8),
% 1.29/0.53    inference(superposition,[],[f151,f48])).
% 1.29/0.53  fof(f48,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 1.29/0.53    inference(equality_resolution,[],[f30])).
% 1.29/0.53  fof(f30,plain,(
% 1.29/0.53    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3) )),
% 1.29/0.53    inference(cnf_transformation,[],[f13])).
% 1.29/0.53  fof(f13,plain,(
% 1.29/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.29/0.53    inference(flattening,[],[f12])).
% 1.29/0.53  fof(f12,plain,(
% 1.29/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f5])).
% 1.29/0.53  fof(f5,axiom,(
% 1.29/0.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).
% 1.29/0.53  fof(f151,plain,(
% 1.29/0.53    ~v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | spl5_8),
% 1.29/0.53    inference(avatar_component_clause,[],[f150])).
% 1.29/0.53  fof(f150,plain,(
% 1.29/0.53    spl5_8 <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.29/0.53  fof(f143,plain,(
% 1.29/0.53    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl5_6),
% 1.29/0.53    inference(resolution,[],[f93,f34])).
% 1.29/0.53  fof(f34,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f14])).
% 1.29/0.53  fof(f14,plain,(
% 1.29/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f3])).
% 1.29/0.53  fof(f3,axiom,(
% 1.29/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.29/0.53  fof(f93,plain,(
% 1.29/0.53    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl5_6),
% 1.29/0.53    inference(avatar_component_clause,[],[f91])).
% 1.29/0.53  fof(f91,plain,(
% 1.29/0.53    spl5_6 <=> m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.29/0.53  fof(f187,plain,(
% 1.29/0.53    ~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_8 | spl5_10),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f186])).
% 1.29/0.53  fof(f186,plain,(
% 1.29/0.53    $false | (~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_8 | spl5_10)),
% 1.29/0.53    inference(subsumption_resolution,[],[f185,f162])).
% 1.29/0.53  fof(f162,plain,(
% 1.29/0.53    ~v1_xboole_0(u1_struct_0(sK2)) | spl5_10),
% 1.29/0.53    inference(avatar_component_clause,[],[f160])).
% 1.29/0.53  fof(f160,plain,(
% 1.29/0.53    spl5_10 <=> v1_xboole_0(u1_struct_0(sK2))),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.29/0.53  fof(f185,plain,(
% 1.29/0.53    v1_xboole_0(u1_struct_0(sK2)) | (~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_8)),
% 1.29/0.53    inference(resolution,[],[f184,f35])).
% 1.29/0.53  fof(f35,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f15])).
% 1.29/0.53  fof(f15,plain,(
% 1.29/0.53    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0))),
% 1.29/0.53    inference(ennf_transformation,[],[f2])).
% 1.29/0.53  fof(f2,axiom,(
% 1.29/0.53    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X1,X0)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).
% 1.29/0.53  fof(f184,plain,(
% 1.29/0.53    v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_8)),
% 1.29/0.53    inference(subsumption_resolution,[],[f183,f26])).
% 1.29/0.53  fof(f183,plain,(
% 1.29/0.53    v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_8)),
% 1.29/0.53    inference(subsumption_resolution,[],[f182,f80])).
% 1.29/0.53  fof(f182,plain,(
% 1.29/0.53    v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | (~spl5_4 | spl5_5 | ~spl5_8)),
% 1.29/0.53    inference(subsumption_resolution,[],[f181,f84])).
% 1.29/0.53  fof(f181,plain,(
% 1.29/0.53    v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | (spl5_5 | ~spl5_8)),
% 1.29/0.53    inference(subsumption_resolution,[],[f180,f88])).
% 1.29/0.53  fof(f180,plain,(
% 1.29/0.53    v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~spl5_8),
% 1.29/0.53    inference(subsumption_resolution,[],[f179,f23])).
% 1.29/0.53  fof(f179,plain,(
% 1.29/0.53    v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~spl5_8),
% 1.29/0.53    inference(subsumption_resolution,[],[f178,f22])).
% 1.29/0.53  fof(f178,plain,(
% 1.29/0.53    v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~spl5_8),
% 1.29/0.53    inference(subsumption_resolution,[],[f177,f25])).
% 1.29/0.53  fof(f177,plain,(
% 1.29/0.53    v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~spl5_8),
% 1.29/0.53    inference(subsumption_resolution,[],[f176,f24])).
% 1.29/0.53  fof(f176,plain,(
% 1.29/0.53    v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~spl5_8),
% 1.29/0.53    inference(subsumption_resolution,[],[f164,f28])).
% 1.29/0.53  fof(f164,plain,(
% 1.29/0.53    v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~spl5_8),
% 1.29/0.53    inference(superposition,[],[f152,f48])).
% 1.29/0.53  fof(f152,plain,(
% 1.29/0.53    v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl5_8),
% 1.29/0.53    inference(avatar_component_clause,[],[f150])).
% 1.29/0.53  fof(f163,plain,(
% 1.29/0.53    ~spl5_10 | ~spl5_2),
% 1.29/0.53    inference(avatar_split_clause,[],[f65,f60,f160])).
% 1.29/0.53  fof(f60,plain,(
% 1.29/0.53    spl5_2 <=> v1_xboole_0(sK3)),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.29/0.53  fof(f65,plain,(
% 1.29/0.53    ~v1_xboole_0(sK3) | ~v1_xboole_0(u1_struct_0(sK2))),
% 1.29/0.53    inference(resolution,[],[f47,f31])).
% 1.29/0.53  fof(f31,plain,(
% 1.29/0.53    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f14])).
% 1.29/0.53  fof(f147,plain,(
% 1.29/0.53    spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f146])).
% 1.29/0.53  fof(f146,plain,(
% 1.29/0.53    $false | (spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5)),
% 1.29/0.53    inference(subsumption_resolution,[],[f145,f52])).
% 1.29/0.53  fof(f145,plain,(
% 1.29/0.53    r2_hidden(sK3,u1_struct_0(sK1)) | (spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5)),
% 1.29/0.53    inference(subsumption_resolution,[],[f144,f64])).
% 1.29/0.53  fof(f144,plain,(
% 1.29/0.53    r2_hidden(sK3,u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK1)) | (spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5)),
% 1.29/0.53    inference(resolution,[],[f141,f51])).
% 1.29/0.53  fof(f141,plain,(
% 1.29/0.53    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5)),
% 1.29/0.53    inference(subsumption_resolution,[],[f140,f26])).
% 1.29/0.53  fof(f140,plain,(
% 1.29/0.53    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK0) | (spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5)),
% 1.29/0.53    inference(subsumption_resolution,[],[f139,f80])).
% 1.29/0.53  fof(f139,plain,(
% 1.29/0.53    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | (spl5_2 | ~spl5_4 | spl5_5)),
% 1.29/0.53    inference(subsumption_resolution,[],[f138,f84])).
% 1.29/0.53  fof(f138,plain,(
% 1.29/0.53    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | (spl5_2 | spl5_5)),
% 1.29/0.53    inference(subsumption_resolution,[],[f137,f88])).
% 1.29/0.53  fof(f137,plain,(
% 1.29/0.53    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_2),
% 1.29/0.53    inference(subsumption_resolution,[],[f136,f23])).
% 1.29/0.53  fof(f136,plain,(
% 1.29/0.53    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_2),
% 1.29/0.53    inference(subsumption_resolution,[],[f135,f22])).
% 1.29/0.53  fof(f135,plain,(
% 1.29/0.53    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_2),
% 1.29/0.53    inference(subsumption_resolution,[],[f134,f25])).
% 1.29/0.53  fof(f134,plain,(
% 1.29/0.53    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_2),
% 1.29/0.53    inference(subsumption_resolution,[],[f133,f24])).
% 1.29/0.53  fof(f133,plain,(
% 1.29/0.53    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_2),
% 1.29/0.53    inference(subsumption_resolution,[],[f132,f28])).
% 1.29/0.53  fof(f132,plain,(
% 1.29/0.53    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_2),
% 1.29/0.53    inference(superposition,[],[f71,f48])).
% 1.29/0.53  fof(f71,plain,(
% 1.29/0.53    r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | spl5_2),
% 1.29/0.53    inference(subsumption_resolution,[],[f68,f70])).
% 1.29/0.53  fof(f70,plain,(
% 1.29/0.53    ~v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | spl5_2),
% 1.29/0.53    inference(subsumption_resolution,[],[f67,f62])).
% 1.29/0.53  fof(f62,plain,(
% 1.29/0.53    ~v1_xboole_0(sK3) | spl5_2),
% 1.29/0.53    inference(avatar_component_clause,[],[f60])).
% 1.29/0.53  fof(f67,plain,(
% 1.29/0.53    v1_xboole_0(sK3) | ~v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 1.29/0.53    inference(resolution,[],[f21,f32])).
% 1.29/0.53  fof(f32,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f14])).
% 1.29/0.53  % (9436)Refutation not found, incomplete strategy% (9436)------------------------------
% 1.29/0.53  % (9436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  fof(f21,plain,(
% 1.29/0.53    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 1.29/0.53    inference(cnf_transformation,[],[f11])).
% 1.29/0.53  % (9436)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  fof(f68,plain,(
% 1.29/0.53    r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 1.29/0.53    inference(resolution,[],[f21,f34])).
% 1.29/0.53  fof(f131,plain,(
% 1.29/0.53    ~spl5_5),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f130])).
% 1.29/0.53  % (9436)Memory used [KB]: 10618
% 1.29/0.53  % (9436)Time elapsed: 0.107 s
% 1.29/0.53  fof(f130,plain,(
% 1.29/0.53    $false | ~spl5_5),
% 1.29/0.53    inference(subsumption_resolution,[],[f129,f26])).
% 1.29/0.53  % (9436)------------------------------
% 1.29/0.53  % (9436)------------------------------
% 1.29/0.53  fof(f129,plain,(
% 1.29/0.53    v2_struct_0(sK0) | ~spl5_5),
% 1.29/0.53    inference(subsumption_resolution,[],[f128,f23])).
% 1.29/0.53  fof(f128,plain,(
% 1.29/0.53    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_5),
% 1.29/0.53    inference(subsumption_resolution,[],[f127,f22])).
% 1.29/0.53  fof(f127,plain,(
% 1.29/0.53    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_5),
% 1.29/0.53    inference(subsumption_resolution,[],[f126,f25])).
% 1.29/0.53  fof(f126,plain,(
% 1.29/0.53    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_5),
% 1.29/0.53    inference(subsumption_resolution,[],[f125,f24])).
% 1.29/0.53  fof(f125,plain,(
% 1.29/0.53    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_5),
% 1.29/0.53    inference(subsumption_resolution,[],[f124,f28])).
% 1.29/0.53  fof(f124,plain,(
% 1.29/0.53    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_5),
% 1.29/0.53    inference(resolution,[],[f89,f37])).
% 1.29/0.53  fof(f37,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f18,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.29/0.53    inference(flattening,[],[f17])).
% 1.29/0.53  fof(f17,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f6])).
% 1.29/0.53  fof(f6,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 1.29/0.53  fof(f89,plain,(
% 1.29/0.53    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_5),
% 1.29/0.53    inference(avatar_component_clause,[],[f87])).
% 1.29/0.53  fof(f111,plain,(
% 1.29/0.53    spl5_3),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f110])).
% 1.29/0.53  fof(f110,plain,(
% 1.29/0.53    $false | spl5_3),
% 1.29/0.53    inference(subsumption_resolution,[],[f109,f26])).
% 1.29/0.53  fof(f109,plain,(
% 1.29/0.53    v2_struct_0(sK0) | spl5_3),
% 1.29/0.53    inference(subsumption_resolution,[],[f108,f23])).
% 1.29/0.53  fof(f108,plain,(
% 1.29/0.53    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_3),
% 1.29/0.53    inference(subsumption_resolution,[],[f107,f22])).
% 1.29/0.53  fof(f107,plain,(
% 1.29/0.53    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_3),
% 1.29/0.53    inference(subsumption_resolution,[],[f106,f25])).
% 1.29/0.53  fof(f106,plain,(
% 1.29/0.53    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_3),
% 1.29/0.53    inference(subsumption_resolution,[],[f105,f24])).
% 1.29/0.53  fof(f105,plain,(
% 1.29/0.53    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_3),
% 1.29/0.53    inference(subsumption_resolution,[],[f104,f28])).
% 1.29/0.53  fof(f104,plain,(
% 1.29/0.53    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_3),
% 1.29/0.53    inference(resolution,[],[f81,f39])).
% 1.29/0.53  fof(f39,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f81,plain,(
% 1.29/0.53    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | spl5_3),
% 1.29/0.53    inference(avatar_component_clause,[],[f79])).
% 1.29/0.53  fof(f102,plain,(
% 1.29/0.53    spl5_4),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f101])).
% 1.29/0.53  fof(f101,plain,(
% 1.29/0.53    $false | spl5_4),
% 1.29/0.53    inference(subsumption_resolution,[],[f100,f26])).
% 1.29/0.53  fof(f100,plain,(
% 1.29/0.53    v2_struct_0(sK0) | spl5_4),
% 1.29/0.53    inference(subsumption_resolution,[],[f99,f23])).
% 1.29/0.53  fof(f99,plain,(
% 1.29/0.53    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_4),
% 1.29/0.53    inference(subsumption_resolution,[],[f98,f22])).
% 1.29/0.53  fof(f98,plain,(
% 1.29/0.53    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_4),
% 1.29/0.53    inference(subsumption_resolution,[],[f97,f25])).
% 1.29/0.53  fof(f97,plain,(
% 1.29/0.53    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_4),
% 1.29/0.53    inference(subsumption_resolution,[],[f96,f24])).
% 1.29/0.53  fof(f96,plain,(
% 1.29/0.53    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_4),
% 1.29/0.53    inference(subsumption_resolution,[],[f95,f28])).
% 1.29/0.53  fof(f95,plain,(
% 1.29/0.53    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_4),
% 1.29/0.53    inference(resolution,[],[f85,f38])).
% 1.29/0.53  fof(f38,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f85,plain,(
% 1.29/0.53    ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | spl5_4),
% 1.29/0.53    inference(avatar_component_clause,[],[f83])).
% 1.29/0.53  fof(f94,plain,(
% 1.29/0.53    ~spl5_3 | ~spl5_4 | spl5_5 | spl5_6),
% 1.29/0.53    inference(avatar_split_clause,[],[f77,f91,f87,f83,f79])).
% 1.29/0.53  fof(f77,plain,(
% 1.29/0.53    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f76,f26])).
% 1.29/0.53  fof(f76,plain,(
% 1.29/0.53    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f75,f23])).
% 1.29/0.53  fof(f75,plain,(
% 1.29/0.53    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f74,f22])).
% 1.29/0.53  fof(f74,plain,(
% 1.29/0.53    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f73,f25])).
% 1.29/0.53  fof(f73,plain,(
% 1.29/0.53    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f72,f24])).
% 1.29/0.53  fof(f72,plain,(
% 1.29/0.53    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f69,f28])).
% 1.29/0.53  fof(f69,plain,(
% 1.29/0.53    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 1.29/0.53    inference(superposition,[],[f21,f48])).
% 1.29/0.53  % SZS output end Proof for theBenchmark
% 1.29/0.53  % (9416)------------------------------
% 1.29/0.53  % (9416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (9416)Termination reason: Refutation
% 1.29/0.53  
% 1.29/0.53  % (9416)Memory used [KB]: 10618
% 1.29/0.53  % (9416)Time elapsed: 0.102 s
% 1.29/0.53  % (9416)------------------------------
% 1.29/0.53  % (9416)------------------------------
% 1.29/0.53  % (9422)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.29/0.54  % (9424)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.29/0.54  % (9414)Success in time 0.166 s
%------------------------------------------------------------------------------
