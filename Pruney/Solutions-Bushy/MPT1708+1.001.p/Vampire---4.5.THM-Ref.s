%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1708+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 361 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          :  522 (3005 expanded)
%              Number of equality atoms :   25 ( 375 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f82,f114,f123,f144,f162,f164,f208])).

fof(f208,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_5
    | spl5_7 ),
    inference(subsumption_resolution,[],[f206,f146])).

fof(f146,plain,
    ( l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f145,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
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
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
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
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
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
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
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
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).

fof(f145,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_5 ),
    inference(resolution,[],[f92,f36])).

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

fof(f92,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_5
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f206,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_4
    | spl5_7 ),
    inference(resolution,[],[f168,f35])).

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

fof(f168,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_4
    | spl5_7 ),
    inference(subsumption_resolution,[],[f166,f100])).

fof(f100,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_7
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f166,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_4 ),
    inference(resolution,[],[f81,f37])).

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

fof(f81,plain,
    ( v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_4
  <=> v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f164,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f160,f70])).

fof(f70,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | spl5_1 ),
    inference(resolution,[],[f60,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f60,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_1
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f160,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(resolution,[],[f157,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f157,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f156,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f156,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f155,f92])).

fof(f155,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f154,f96])).

fof(f96,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_6
  <=> v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f154,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | spl5_7 ),
    inference(subsumption_resolution,[],[f153,f100])).

fof(f153,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f152,f29])).

fof(f29,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f152,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f151,f28])).

fof(f28,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f151,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f150,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f150,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f149,f31])).

fof(f31,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f149,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f148,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f148,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f147,f34])).

fof(f147,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(superposition,[],[f77,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
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
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
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
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f77,plain,
    ( r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_3
  <=> r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f162,plain,
    ( spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f159,f71])).

fof(f71,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | spl5_2 ),
    inference(resolution,[],[f64,f40])).

fof(f64,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f159,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(resolution,[],[f157,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f144,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f142,f32])).

fof(f142,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f141,f28])).

fof(f141,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f140,f27])).

fof(f140,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f139,f31])).

fof(f139,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f138,f30])).

fof(f138,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f137,f34])).

fof(f137,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f101,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f101,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f123,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f121,f32])).

fof(f121,plain,
    ( v2_struct_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f120,f28])).

fof(f120,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f119,f27])).

fof(f119,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f118,f31])).

fof(f118,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f117,f30])).

fof(f117,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f116,f34])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_5 ),
    inference(resolution,[],[f93,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f114,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl5_6 ),
    inference(subsumption_resolution,[],[f112,f32])).

fof(f112,plain,
    ( v2_struct_0(sK0)
    | spl5_6 ),
    inference(subsumption_resolution,[],[f111,f28])).

fof(f111,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_6 ),
    inference(subsumption_resolution,[],[f110,f27])).

fof(f110,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_6 ),
    inference(subsumption_resolution,[],[f109,f31])).

fof(f109,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_6 ),
    inference(subsumption_resolution,[],[f108,f30])).

fof(f108,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_6 ),
    inference(subsumption_resolution,[],[f107,f34])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_6 ),
    inference(resolution,[],[f97,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,
    ( ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f82,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f72,f79,f75])).

fof(f72,plain,
    ( v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(resolution,[],[f26,f41])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f26,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f52,f62,f58])).

fof(f52,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | sK3 != X5
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
