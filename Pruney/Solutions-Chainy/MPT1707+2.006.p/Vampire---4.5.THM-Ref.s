%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 424 expanded)
%              Number of leaves         :   18 (  83 expanded)
%              Depth                    :   17
%              Number of atoms          :  588 (3182 expanded)
%              Number of equality atoms :   23 ( 422 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f90,f128,f136,f145,f165,f191,f211,f217,f226,f231])).

fof(f231,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f229,f61])).

fof(f61,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f60,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
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

% (14778)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tmap_1)).

fof(f60,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f29,f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f29,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f229,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f228,f35])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f228,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f227,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f227,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f85,f37])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f85,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_4
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f226,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f224,f63])).

fof(f63,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f62,f34])).

fof(f62,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f31,f36])).

fof(f31,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f224,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f223,f35])).

fof(f223,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f222,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f222,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f68,f37])).

fof(f68,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_1
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f217,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_8
    | spl5_10 ),
    inference(subsumption_resolution,[],[f215,f167])).

fof(f167,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f166,f34])).

fof(f166,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_8 ),
    inference(resolution,[],[f114,f36])).

fof(f114,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_8
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f215,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_7
    | spl5_10 ),
    inference(resolution,[],[f214,f35])).

fof(f214,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_7
    | spl5_10 ),
    inference(subsumption_resolution,[],[f212,f122])).

fof(f122,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_10
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f212,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_7 ),
    inference(resolution,[],[f102,f37])).

fof(f102,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_7
  <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f211,plain,
    ( spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f155,f209])).

fof(f209,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10 ),
    inference(subsumption_resolution,[],[f208,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f208,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK0)
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10 ),
    inference(subsumption_resolution,[],[f207,f114])).

fof(f207,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_7
    | ~ spl5_9
    | spl5_10 ),
    inference(subsumption_resolution,[],[f206,f118])).

fof(f118,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_9
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f206,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_7
    | spl5_10 ),
    inference(subsumption_resolution,[],[f205,f122])).

fof(f205,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f204,f29])).

fof(f204,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f203,f28])).

fof(f203,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f202,f31])).

fof(f202,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f201,f30])).

fof(f201,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f186,f34])).

fof(f186,plain,
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
    | spl5_7 ),
    inference(superposition,[],[f101,f56])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f101,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f155,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl5_12
  <=> v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f191,plain,
    ( spl5_3
    | spl5_5
    | ~ spl5_11
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl5_3
    | spl5_5
    | ~ spl5_11
    | spl5_12 ),
    inference(subsumption_resolution,[],[f189,f78])).

fof(f78,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_3
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f189,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | spl5_5
    | ~ spl5_11
    | spl5_12 ),
    inference(subsumption_resolution,[],[f188,f89])).

fof(f89,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_5
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f188,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl5_11
    | spl5_12 ),
    inference(resolution,[],[f185,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f185,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_11
    | spl5_12 ),
    inference(subsumption_resolution,[],[f180,f156])).

fof(f156,plain,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f180,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_11 ),
    inference(resolution,[],[f127,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f127,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_11
  <=> m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f165,plain,(
    ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f163,f32])).

fof(f163,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f162,f29])).

fof(f162,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f161,f28])).

fof(f161,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f160,f31])).

fof(f160,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f159,f30])).

fof(f159,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f158,f34])).

fof(f158,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f123,f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f123,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f145,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl5_8 ),
    inference(subsumption_resolution,[],[f143,f32])).

fof(f143,plain,
    ( v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f142,f29])).

fof(f142,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f141,f28])).

fof(f141,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f140,f31])).

fof(f140,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f139,f30])).

fof(f139,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f138,f34])).

fof(f138,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(resolution,[],[f115,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f115,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f136,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl5_9 ),
    inference(subsumption_resolution,[],[f134,f32])).

fof(f134,plain,
    ( v2_struct_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f133,f29])).

fof(f133,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f132,f28])).

fof(f132,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f131,f31])).

fof(f131,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f130,f30])).

fof(f130,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f129,f34])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_9 ),
    inference(resolution,[],[f119,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f119,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f128,plain,
    ( ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | spl5_11 ),
    inference(avatar_split_clause,[],[f111,f125,f121,f117,f113])).

fof(f111,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f110,f32])).

fof(f110,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f29])).

fof(f109,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f108,f28])).

fof(f108,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f107,f31])).

fof(f107,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f106,f30])).

fof(f106,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f94,f34])).

fof(f94,plain,
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
    inference(superposition,[],[f27,f56])).

fof(f27,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f90,plain,
    ( spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f81,f87,f83])).

fof(f81,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f65,f76,f67])).

fof(f65,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f54,f42])).

fof(f54,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | sK3 != X5 ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (14789)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (14777)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.46  % (14773)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (14783)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (14791)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (14790)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (14787)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (14781)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (14775)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (14775)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f79,f90,f128,f136,f145,f165,f191,f211,f217,f226,f231])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    ~spl5_4),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f230])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    $false | ~spl5_4),
% 0.20/0.50    inference(subsumption_resolution,[],[f229,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    l1_pre_topc(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f60,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  % (14778)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 0.20/0.50    inference(rectify,[],[f10])).
% 0.20/0.50  fof(f10,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f9])).
% 0.20/0.50  fof(f9,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tmap_1)).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.20/0.50    inference(resolution,[],[f29,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    m1_pre_topc(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f229,plain,(
% 0.20/0.50    ~l1_pre_topc(sK2) | ~spl5_4),
% 0.20/0.50    inference(resolution,[],[f228,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    ~l1_struct_0(sK2) | ~spl5_4),
% 0.20/0.50    inference(subsumption_resolution,[],[f227,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ~v2_struct_0(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl5_4),
% 0.20/0.50    inference(resolution,[],[f85,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    v1_xboole_0(u1_struct_0(sK2)) | ~spl5_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    spl5_4 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    ~spl5_1),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f225])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    $false | ~spl5_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f224,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    l1_pre_topc(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f62,f34])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 0.20/0.50    inference(resolution,[],[f31,f36])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    ~l1_pre_topc(sK1) | ~spl5_1),
% 0.20/0.50    inference(resolution,[],[f223,f35])).
% 0.20/0.50  fof(f223,plain,(
% 0.20/0.50    ~l1_struct_0(sK1) | ~spl5_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f222,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_1),
% 0.20/0.50    inference(resolution,[],[f68,f37])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    v1_xboole_0(u1_struct_0(sK1)) | ~spl5_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    spl5_1 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    ~spl5_7 | ~spl5_8 | spl5_10),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f216])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    $false | (~spl5_7 | ~spl5_8 | spl5_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f215,f167])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f166,f34])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_8),
% 0.20/0.50    inference(resolution,[],[f114,f36])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | ~spl5_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f113])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    spl5_8 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.50  fof(f215,plain,(
% 0.20/0.50    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | (~spl5_7 | spl5_10)),
% 0.20/0.50    inference(resolution,[],[f214,f35])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    ~l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | (~spl5_7 | spl5_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f212,f122])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | spl5_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f121])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    spl5_10 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    ~l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_7),
% 0.20/0.50    inference(resolution,[],[f102,f37])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl5_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    spl5_7 <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    spl5_7 | ~spl5_8 | ~spl5_9 | spl5_10 | ~spl5_12),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f210])).
% 0.20/0.50  fof(f210,plain,(
% 0.20/0.50    $false | (spl5_7 | ~spl5_8 | ~spl5_9 | spl5_10 | ~spl5_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f155,f209])).
% 0.20/0.50  fof(f209,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (spl5_7 | ~spl5_8 | ~spl5_9 | spl5_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f208,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK0) | (spl5_7 | ~spl5_8 | ~spl5_9 | spl5_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f207,f114])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | (spl5_7 | ~spl5_9 | spl5_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f206,f118])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f117])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    spl5_9 <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | (spl5_7 | spl5_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f205,f122])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_7),
% 0.20/0.50    inference(subsumption_resolution,[],[f204,f29])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_7),
% 0.20/0.50    inference(subsumption_resolution,[],[f203,f28])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_7),
% 0.20/0.50    inference(subsumption_resolution,[],[f202,f31])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_7),
% 0.20/0.50    inference(subsumption_resolution,[],[f201,f30])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_7),
% 0.20/0.50    inference(subsumption_resolution,[],[f186,f34])).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_7),
% 0.20/0.50    inference(superposition,[],[f101,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ~v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | spl5_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f100])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl5_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f154])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    spl5_12 <=> v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    spl5_3 | spl5_5 | ~spl5_11 | spl5_12),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f190])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    $false | (spl5_3 | spl5_5 | ~spl5_11 | spl5_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f189,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ~r2_hidden(sK3,u1_struct_0(sK1)) | spl5_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl5_3 <=> r2_hidden(sK3,u1_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    r2_hidden(sK3,u1_struct_0(sK1)) | (spl5_5 | ~spl5_11 | spl5_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f188,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ~r2_hidden(sK3,u1_struct_0(sK2)) | spl5_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl5_5 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    r2_hidden(sK3,u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK1)) | (~spl5_11 | spl5_12)),
% 0.20/0.50    inference(resolution,[],[f185,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl5_11 | spl5_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f180,f156])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | spl5_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f154])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl5_11),
% 0.20/0.50    inference(resolution,[],[f127,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl5_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f125])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    spl5_11 <=> m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ~spl5_10),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f164])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    $false | ~spl5_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f163,f32])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~spl5_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f162,f29])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f161,f28])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f160,f31])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f159,f30])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f158,f34])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_10),
% 0.20/0.50    inference(resolution,[],[f123,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f121])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    spl5_8),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f144])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    $false | spl5_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f143,f32])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    v2_struct_0(sK0) | spl5_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f142,f29])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f141,f28])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f140,f31])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f139,f30])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f138,f34])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_8),
% 0.20/0.50    inference(resolution,[],[f115,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | spl5_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f113])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    spl5_9),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    $false | spl5_9),
% 0.20/0.50    inference(subsumption_resolution,[],[f134,f32])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    v2_struct_0(sK0) | spl5_9),
% 0.20/0.50    inference(subsumption_resolution,[],[f133,f29])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_9),
% 0.20/0.50    inference(subsumption_resolution,[],[f132,f28])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_9),
% 0.20/0.50    inference(subsumption_resolution,[],[f131,f31])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_9),
% 0.20/0.50    inference(subsumption_resolution,[],[f130,f30])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_9),
% 0.20/0.50    inference(subsumption_resolution,[],[f129,f34])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_9),
% 0.20/0.50    inference(resolution,[],[f119,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | spl5_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f117])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ~spl5_8 | ~spl5_9 | spl5_10 | spl5_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f111,f125,f121,f117,f113])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f110,f32])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f109,f29])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f108,f28])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f107,f31])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f106,f30])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f94,f34])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(superposition,[],[f27,f56])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    spl5_4 | ~spl5_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f81,f87,f83])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ~r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.50    inference(resolution,[],[f55,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.20/0.50    inference(equality_resolution,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X4) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl5_1 | ~spl5_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f65,f76,f67])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ~r2_hidden(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.50    inference(resolution,[],[f54,f42])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.20/0.50    inference(equality_resolution,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK1)) | sK3 != X5) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (14775)------------------------------
% 0.20/0.50  % (14775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (14775)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (14775)Memory used [KB]: 10618
% 0.20/0.50  % (14775)Time elapsed: 0.092 s
% 0.20/0.50  % (14775)------------------------------
% 0.20/0.50  % (14775)------------------------------
% 0.20/0.50  % (14780)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (14771)Success in time 0.15 s
%------------------------------------------------------------------------------
