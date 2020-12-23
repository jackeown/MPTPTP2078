%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t17_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:50 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 493 expanded)
%              Number of leaves         :   52 ( 203 expanded)
%              Depth                    :   15
%              Number of atoms          : 1183 (2155 expanded)
%              Number of equality atoms :   22 (  52 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f485,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f129,f136,f143,f150,f157,f164,f171,f178,f185,f198,f199,f210,f219,f240,f281,f298,f310,f332,f337,f348,f355,f359,f363,f372,f405,f408,f447,f453,f459,f470,f474,f480,f484])).

fof(f484,plain,
    ( ~ spl5_20
    | spl5_23
    | ~ spl5_24
    | ~ spl5_66 ),
    inference(avatar_contradiction_clause,[],[f483])).

fof(f483,plain,
    ( $false
    | ~ spl5_20
    | ~ spl5_23
    | ~ spl5_24
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f482,f194])).

fof(f194,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl5_23
  <=> ~ r1_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f482,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ spl5_20
    | ~ spl5_24
    | ~ spl5_66 ),
    inference(subsumption_resolution,[],[f481,f209])).

fof(f209,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl5_24
  <=> m1_subset_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f481,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ spl5_20
    | ~ spl5_66 ),
    inference(resolution,[],[f191,f446])).

fof(f446,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r1_waybel_7(sK0,sK1,X0) )
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl5_66
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | r1_waybel_7(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f191,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl5_20
  <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f480,plain,
    ( spl5_21
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_68 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_68 ),
    inference(subsumption_resolution,[],[f478,f197])).

fof(f197,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl5_22
  <=> r1_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f478,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ spl5_21
    | ~ spl5_24
    | ~ spl5_68 ),
    inference(subsumption_resolution,[],[f475,f209])).

fof(f475,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ spl5_21
    | ~ spl5_68 ),
    inference(resolution,[],[f473,f188])).

fof(f188,plain,
    ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl5_21
  <=> ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f473,plain,
    ( ! [X1] :
        ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
        | ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK1,X1) )
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl5_68
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
        | ~ r1_waybel_7(sK0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f474,plain,
    ( ~ spl5_61
    | ~ spl5_63
    | ~ spl5_65
    | spl5_44
    | spl5_68
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_26
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f321,f308,f217,f141,f134,f127,f472,f350,f442,f436,f430])).

fof(f430,plain,
    ( spl5_61
  <=> ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f436,plain,
    ( spl5_63
  <=> ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f442,plain,
    ( spl5_65
  <=> ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f350,plain,
    ( spl5_44
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f127,plain,
    ( spl5_3
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f134,plain,
    ( spl5_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f141,plain,
    ( spl5_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f217,plain,
    ( spl5_26
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f308,plain,
    ( spl5_36
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f321,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK1,X1)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_26
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f320,f218])).

fof(f218,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f217])).

fof(f320,plain,
    ( ! [X1] :
        ( ~ r1_waybel_7(sK0,sK1,X1)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f319,f128])).

fof(f128,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f319,plain,
    ( ! [X1] :
        ( ~ r1_waybel_7(sK0,sK1,X1)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) )
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f318,f142])).

fof(f142,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f141])).

fof(f318,plain,
    ( ! [X1] :
        ( ~ r1_waybel_7(sK0,sK1,X1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) )
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f312,f135])).

fof(f135,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f312,plain,
    ( ! [X1] :
        ( ~ r1_waybel_7(sK0,sK1,X1)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) )
    | ~ spl5_36 ),
    inference(superposition,[],[f88,f309])).

fof(f309,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f308])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',t12_yellow19)).

fof(f470,plain,
    ( spl5_1
    | spl5_3
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_26
    | ~ spl5_32
    | ~ spl5_34
    | spl5_39
    | spl5_61 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_26
    | ~ spl5_32
    | ~ spl5_34
    | ~ spl5_39
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f468,f280])).

fof(f280,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl5_34
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f468,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_26
    | ~ spl5_32
    | ~ spl5_39
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f467,f218])).

fof(f467,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_32
    | ~ spl5_39
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f466,f128])).

fof(f466,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_32
    | ~ spl5_39
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f465,f177])).

fof(f177,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl5_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f465,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_32
    | ~ spl5_39
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f464,f163])).

fof(f163,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl5_12
  <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f464,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_32
    | ~ spl5_39
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f463,f156])).

fof(f156,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_10
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f463,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_32
    | ~ spl5_39
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f462,f121])).

fof(f121,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_1
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f462,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl5_32
    | ~ spl5_39
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f461,f325])).

fof(f325,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl5_39
  <=> ~ v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f461,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl5_32
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f460,f271])).

fof(f271,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl5_32
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f460,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl5_61 ),
    inference(resolution,[],[f431,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',dt_k3_yellow19)).

fof(f431,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f430])).

fof(f459,plain,
    ( spl5_3
    | ~ spl5_26
    | ~ spl5_32
    | ~ spl5_34
    | ~ spl5_46
    | spl5_65 ),
    inference(avatar_contradiction_clause,[],[f458])).

fof(f458,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_26
    | ~ spl5_32
    | ~ spl5_34
    | ~ spl5_46
    | ~ spl5_65 ),
    inference(subsumption_resolution,[],[f457,f280])).

fof(f457,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_26
    | ~ spl5_32
    | ~ spl5_46
    | ~ spl5_65 ),
    inference(forward_demodulation,[],[f456,f218])).

fof(f456,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_32
    | ~ spl5_46
    | ~ spl5_65 ),
    inference(subsumption_resolution,[],[f455,f128])).

fof(f455,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_32
    | ~ spl5_46
    | ~ spl5_65 ),
    inference(subsumption_resolution,[],[f454,f271])).

fof(f454,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_46
    | ~ spl5_65 ),
    inference(resolution,[],[f443,f358])).

fof(f358,plain,
    ( ! [X5] :
        ( v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1))
        | ~ l1_struct_0(X5)
        | v2_struct_0(X5)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) )
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl5_46
  <=> ! [X5] :
        ( ~ l1_struct_0(X5)
        | v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1))
        | v2_struct_0(X5)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f443,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f442])).

fof(f453,plain,
    ( spl5_3
    | ~ spl5_26
    | ~ spl5_32
    | ~ spl5_34
    | ~ spl5_48
    | spl5_63 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_26
    | ~ spl5_32
    | ~ spl5_34
    | ~ spl5_48
    | ~ spl5_63 ),
    inference(subsumption_resolution,[],[f451,f280])).

fof(f451,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_26
    | ~ spl5_32
    | ~ spl5_48
    | ~ spl5_63 ),
    inference(forward_demodulation,[],[f450,f218])).

fof(f450,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_32
    | ~ spl5_48
    | ~ spl5_63 ),
    inference(subsumption_resolution,[],[f449,f128])).

fof(f449,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_32
    | ~ spl5_48
    | ~ spl5_63 ),
    inference(subsumption_resolution,[],[f448,f271])).

fof(f448,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_48
    | ~ spl5_63 ),
    inference(resolution,[],[f437,f362])).

fof(f362,plain,
    ( ! [X5] :
        ( v7_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1))
        | ~ l1_struct_0(X5)
        | v2_struct_0(X5)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) )
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl5_48
  <=> ! [X5] :
        ( ~ l1_struct_0(X5)
        | v7_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1))
        | v2_struct_0(X5)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f437,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f436])).

fof(f447,plain,
    ( ~ spl5_61
    | ~ spl5_63
    | ~ spl5_65
    | spl5_44
    | spl5_66
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_26
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f317,f308,f217,f141,f134,f127,f445,f350,f442,f436,f430])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r1_waybel_7(sK0,sK1,X0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_26
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f316,f218])).

fof(f316,plain,
    ( ! [X0] :
        ( r1_waybel_7(sK0,sK1,X0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f315,f128])).

fof(f315,plain,
    ( ! [X0] :
        ( r1_waybel_7(sK0,sK1,X0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f314,f142])).

fof(f314,plain,
    ( ! [X0] :
        ( r1_waybel_7(sK0,sK1,X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f311,f135])).

fof(f311,plain,
    ( ! [X0] :
        ( r1_waybel_7(sK0,sK1,X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | ~ spl5_36 ),
    inference(superposition,[],[f89,f309])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f408,plain,
    ( ~ spl5_18
    | spl5_53 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | ~ spl5_18
    | ~ spl5_53 ),
    inference(subsumption_resolution,[],[f406,f184])).

fof(f184,plain,
    ( l1_pre_topc(sK4)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl5_18
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f406,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl5_53 ),
    inference(resolution,[],[f386,f115])).

fof(f115,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',dt_l1_pre_topc)).

fof(f386,plain,
    ( ~ l1_struct_0(sK4)
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl5_53
  <=> ~ l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f405,plain,
    ( ~ spl5_53
    | spl5_54
    | ~ spl5_57
    | ~ spl5_59
    | ~ spl5_40
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f377,f370,f330,f403,f397,f391,f385])).

fof(f391,plain,
    ( spl5_54
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f397,plain,
    ( spl5_57
  <=> ~ v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f403,plain,
    ( spl5_59
  <=> ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f330,plain,
    ( spl5_40
  <=> ! [X5] :
        ( ~ l1_struct_0(X5)
        | ~ v2_struct_0(k3_yellow19(X5,k2_struct_0(sK0),sK1))
        | v2_struct_0(X5)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f370,plain,
    ( spl5_50
  <=> k2_struct_0(sK4) = u1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f377,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK4)))
    | ~ v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | ~ spl5_40
    | ~ spl5_50 ),
    inference(superposition,[],[f331,f371])).

fof(f371,plain,
    ( k2_struct_0(sK4) = u1_struct_0(sK4)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f370])).

fof(f331,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v2_struct_0(k3_yellow19(X5,k2_struct_0(sK0),sK1))
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5) )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f330])).

fof(f372,plain,
    ( spl5_50
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f202,f183,f370])).

fof(f202,plain,
    ( k2_struct_0(sK4) = u1_struct_0(sK4)
    | ~ spl5_18 ),
    inference(resolution,[],[f200,f184])).

fof(f200,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f108,f115])).

fof(f108,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',d3_struct_0)).

fof(f363,plain,
    ( spl5_38
    | spl5_48
    | spl5_1
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f290,f176,f169,f162,f155,f120,f361,f327])).

fof(f327,plain,
    ( spl5_38
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f169,plain,
    ( spl5_14
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f290,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | v7_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f289,f163])).

fof(f289,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | v7_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f288,f156])).

fof(f288,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | v7_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f287,f170])).

fof(f170,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f287,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | v7_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f284,f121])).

fof(f284,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | v1_xboole_0(sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | v7_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f92,f177])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | v2_struct_0(X0)
      | v7_waybel_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',fc5_yellow19)).

fof(f359,plain,
    ( spl5_38
    | spl5_46
    | spl5_1
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f264,f176,f162,f155,f120,f357,f327])).

fof(f264,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f263,f163])).

fof(f263,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f262,f156])).

fof(f262,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f259,f121])).

fof(f259,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | v1_xboole_0(sK1)
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | v4_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f98,f177])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | v2_struct_0(X0)
      | v4_orders_2(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',fc4_yellow19)).

fof(f355,plain,
    ( ~ spl5_45
    | spl5_3
    | ~ spl5_32
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f344,f330,f270,f127,f353])).

fof(f353,plain,
    ( spl5_45
  <=> ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f344,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl5_3
    | ~ spl5_32
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f343,f271])).

fof(f343,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f342,f128])).

fof(f342,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl5_40 ),
    inference(duplicate_literal_removal,[],[f340])).

fof(f340,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl5_40 ),
    inference(resolution,[],[f331,f106])).

fof(f106,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',dt_k2_struct_0)).

fof(f348,plain,
    ( spl5_38
    | spl5_42
    | spl5_1
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f256,f176,f162,f155,f120,f346,f327])).

fof(f346,plain,
    ( spl5_42
  <=> ! [X5] :
        ( ~ l1_struct_0(X5)
        | v3_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1))
        | v2_struct_0(X5)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f256,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | v3_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f255,f163])).

fof(f255,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | v3_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f254,f156])).

fof(f254,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | v3_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f251,f121])).

fof(f251,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | v1_xboole_0(sK1)
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | v3_orders_2(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f97,f177])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | v2_struct_0(X0)
      | v3_orders_2(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f337,plain,
    ( spl5_3
    | ~ spl5_32
    | ~ spl5_38 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_32
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f335,f128])).

fof(f335,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_32
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f333,f271])).

fof(f333,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_38 ),
    inference(resolution,[],[f328,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',fc5_struct_0)).

fof(f328,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f327])).

fof(f332,plain,
    ( spl5_38
    | spl5_40
    | spl5_1
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f248,f176,f162,f155,f120,f330,f327])).

fof(f248,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v2_struct_0(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f247,f163])).

fof(f247,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | ~ v2_struct_0(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f246,f156])).

fof(f246,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | ~ v2_struct_0(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_1
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f243,f121])).

fof(f243,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
        | v1_xboole_0(sK1)
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X5)
        | ~ v2_struct_0(k3_yellow19(X5,k2_struct_0(sK0),sK1)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f93,f177])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | v2_struct_0(X0)
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f310,plain,
    ( spl5_36
    | ~ spl5_33
    | spl5_1
    | spl5_3
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f303,f176,f169,f162,f155,f127,f120,f273,f308])).

fof(f273,plain,
    ( spl5_33
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f303,plain,
    ( ~ l1_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f302,f128])).

fof(f302,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f301,f163])).

fof(f301,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f300,f156])).

fof(f300,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f299,f170])).

fof(f299,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl5_1
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f293,f121])).

fof(f293,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl5_16 ),
    inference(resolution,[],[f100,f177])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v2_struct_0(X0)
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',t15_yellow19)).

fof(f298,plain,
    ( ~ spl5_6
    | spl5_33 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f296,f142])).

fof(f296,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_33 ),
    inference(resolution,[],[f274,f115])).

fof(f274,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f273])).

fof(f281,plain,
    ( ~ spl5_33
    | spl5_34
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f226,f217,f279,f273])).

fof(f226,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl5_26 ),
    inference(superposition,[],[f106,f218])).

fof(f240,plain,
    ( ~ spl5_29
    | spl5_30
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f221,f176,f238,f235])).

fof(f235,plain,
    ( spl5_29
  <=> ~ v1_xboole_0(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f238,plain,
    ( spl5_30
  <=> ! [X2] : ~ r2_hidden(X2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f221,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ v1_xboole_0(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl5_16 ),
    inference(resolution,[],[f101,f177])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',t5_subset)).

fof(f219,plain,
    ( spl5_26
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f201,f141,f217])).

fof(f201,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f200,f142])).

fof(f210,plain,
    ( spl5_24
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f203,f148,f141,f208])).

fof(f148,plain,
    ( spl5_8
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f203,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f201,f149])).

fof(f149,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f199,plain,
    ( ~ spl5_21
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f78,f193,f187])).

fof(f78,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',t17_yellow19)).

fof(f198,plain,
    ( spl5_20
    | spl5_22 ),
    inference(avatar_split_clause,[],[f77,f196,f190])).

fof(f77,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f185,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f114,f183])).

fof(f114,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t17_yellow19.p',existence_l1_pre_topc)).

fof(f178,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f84,f176])).

fof(f84,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f51])).

fof(f171,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f81,f169])).

fof(f81,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f164,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f83,f162])).

fof(f83,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f157,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f82,f155])).

fof(f82,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f150,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f79,f148])).

fof(f79,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f143,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f87,f141])).

fof(f87,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f136,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f86,f134])).

fof(f86,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f129,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f85,f127])).

fof(f85,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f122,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f80,f120])).

fof(f80,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
