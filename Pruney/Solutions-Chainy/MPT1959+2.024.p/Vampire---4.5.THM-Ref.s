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
% DateTime   : Thu Dec  3 13:22:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 336 expanded)
%              Number of leaves         :   38 ( 117 expanded)
%              Depth                    :   18
%              Number of atoms          :  736 (1448 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f617,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f109,f114,f146,f151,f156,f171,f216,f222,f227,f239,f266,f273,f313,f319,f447,f471,f538,f603,f611,f616])).

fof(f616,plain,
    ( ~ spl6_12
    | ~ spl6_16
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f614,f238])).

fof(f238,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl6_16 ),
    inference(resolution,[],[f199,f79])).

fof(f79,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f199,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl6_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f614,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl6_12
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f166,f256])).

fof(f256,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl6_22
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f166,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl6_12
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f611,plain,
    ( spl6_1
    | spl6_13
    | ~ spl6_35 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | spl6_1
    | spl6_13
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f609,f170])).

fof(f170,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_13
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f609,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | spl6_1
    | ~ spl6_35 ),
    inference(resolution,[],[f602,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(X0,sK1) )
    | spl6_1 ),
    inference(resolution,[],[f83,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f83,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f602,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f600])).

fof(f600,plain,
    ( spl6_35
  <=> m1_subset_1(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f603,plain,
    ( spl6_35
    | ~ spl6_7
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f439,f254,f111,f600])).

fof(f111,plain,
    ( spl6_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f439,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ spl6_7
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f431,f113])).

fof(f113,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f431,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl6_22 ),
    inference(superposition,[],[f53,f256])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f538,plain,
    ( spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_19
    | spl6_23
    | ~ spl6_24
    | ~ spl6_27 ),
    inference(avatar_contradiction_clause,[],[f537])).

fof(f537,plain,
    ( $false
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_19
    | spl6_23
    | ~ spl6_24
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f532,f272])).

fof(f272,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl6_24
  <=> m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f532,plain,
    ( ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_19
    | spl6_23
    | ~ spl6_27 ),
    inference(resolution,[],[f528,f265])).

fof(f265,plain,
    ( ~ r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl6_23
  <=> r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f528,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_19
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f527,f169])).

fof(f169,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f527,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_19
    | ~ spl6_27 ),
    inference(duplicate_literal_removal,[],[f526])).

fof(f526,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_19
    | ~ spl6_27 ),
    inference(resolution,[],[f524,f283])).

fof(f283,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,X0)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f282,f145])).

fof(f145,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_9
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f282,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X1,X0)
        | r2_hidden(X0,sK1)
        | ~ v13_waybel_0(sK1,sK0) )
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(resolution,[],[f136,f150])).

fof(f150,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl6_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f136,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ r1_orders_2(sK0,X6,X7)
        | r2_hidden(X7,X5)
        | ~ v13_waybel_0(X5,sK0) )
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f134,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f134,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ r1_orders_2(sK0,X6,X7)
        | r2_hidden(X7,X5)
        | ~ v13_waybel_0(X5,sK0) )
    | ~ spl6_7 ),
    inference(resolution,[],[f113,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f524,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_19
    | ~ spl6_27 ),
    inference(duplicate_literal_removal,[],[f523])).

fof(f523,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_19
    | ~ spl6_27 ),
    inference(superposition,[],[f505,f125])).

fof(f125,plain,
    ( ! [X1] :
        ( k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f124,f113])).

fof(f124,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1 )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f123,f103])).

fof(f103,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_5
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f123,plain,
    ( ! [X1] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1 )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f122,f88])).

fof(f88,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f122,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1 )
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f117,f93])).

fof(f93,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_3
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f117,plain,
    ( ! [X1] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1 )
    | ~ spl6_4 ),
    inference(resolution,[],[f98,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

fof(f98,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f505,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,k5_waybel_0(sK0,X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_19
    | ~ spl6_27 ),
    inference(resolution,[],[f472,f121])).

fof(f121,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK0,k5_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f120,f113])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f119,f103])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f118,f88])).

fof(f118,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) )
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f116,f93])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) )
    | ~ spl6_4 ),
    inference(resolution,[],[f98,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f472,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) )
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_19
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f284,f332])).

fof(f332,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f325,f52])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f325,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ v1_xboole_0(k1_xboole_0) )
    | ~ spl6_27 ),
    inference(resolution,[],[f312,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f312,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl6_27
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f284,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_xboole_0,X0),k1_xboole_0)
        | ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) )
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_19 ),
    inference(resolution,[],[f279,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f279,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))
        | ~ r1_yellow_0(sK0,X0) )
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f277,f226])).

fof(f226,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl6_19
  <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f277,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) )
    | ~ spl6_7
    | ~ spl6_11 ),
    inference(resolution,[],[f130,f155])).

fof(f155,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl6_11
  <=> r1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r1_yellow_0(sK0,X0)
        | ~ r1_tarski(X0,X1)
        | ~ r1_yellow_0(sK0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1)) )
    | ~ spl6_7 ),
    inference(resolution,[],[f113,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_tarski(X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_yellow_0(X0,X2)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f471,plain,
    ( spl6_25
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f470])).

fof(f470,plain,
    ( $false
    | spl6_25
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f468,f294])).

fof(f294,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl6_25
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f468,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_28 ),
    inference(resolution,[],[f318,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f318,plain,
    ( r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl6_28
  <=> r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f447,plain,
    ( spl6_13
    | ~ spl6_10
    | spl6_22 ),
    inference(avatar_split_clause,[],[f446,f254,f148,f168])).

fof(f446,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl6_10
    | spl6_22 ),
    inference(subsumption_resolution,[],[f41,f445])).

fof(f445,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_10
    | spl6_22 ),
    inference(subsumption_resolution,[],[f207,f255])).

fof(f255,plain,
    ( sK1 != u1_struct_0(sK0)
    | spl6_22 ),
    inference(avatar_component_clause,[],[f254])).

fof(f207,plain,
    ( sK1 = u1_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(resolution,[],[f150,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f41,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f319,plain,
    ( spl6_28
    | spl6_25 ),
    inference(avatar_split_clause,[],[f314,f293,f316])).

fof(f314,plain,
    ( r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl6_25 ),
    inference(resolution,[],[f294,f73])).

fof(f313,plain,
    ( spl6_27
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f302,f293,f310])).

fof(f302,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_25 ),
    inference(resolution,[],[f295,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f295,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f293])).

fof(f273,plain,
    ( spl6_22
    | spl6_24
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f161,f148,f270,f254])).

fof(f161,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f150,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f266,plain,
    ( spl6_22
    | ~ spl6_23
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f162,f148,f263,f254])).

fof(f162,plain,
    ( ~ r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f150,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f239,plain,
    ( spl6_15
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f228,f219,f192])).

fof(f192,plain,
    ( spl6_15
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f219,plain,
    ( spl6_18
  <=> r2_hidden(sK5(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f228,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl6_18 ),
    inference(resolution,[],[f221,f74])).

fof(f221,plain,
    ( r2_hidden(sK5(sK1,sK1),sK1)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f219])).

fof(f227,plain,
    ( spl6_19
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f135,f111,f224])).

fof(f135,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl6_7 ),
    inference(resolution,[],[f113,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f222,plain,
    ( spl6_18
    | spl6_15 ),
    inference(avatar_split_clause,[],[f217,f192,f219])).

fof(f217,plain,
    ( r2_hidden(sK5(sK1,sK1),sK1)
    | spl6_15 ),
    inference(resolution,[],[f193,f73])).

fof(f193,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f192])).

fof(f216,plain,
    ( spl6_16
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f202,f192,f197])).

fof(f202,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_15 ),
    inference(resolution,[],[f194,f75])).

fof(f194,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f192])).

fof(f171,plain,
    ( spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f40,f168,f164])).

fof(f40,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f156,plain,
    ( spl6_11
    | spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f129,f111,f106,f101,f86,f153])).

fof(f106,plain,
    ( spl6_6
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f129,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f128,f113])).

fof(f128,plain,
    ( ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0)
    | spl6_2
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f127,f88])).

fof(f127,plain,
    ( v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f126,f103])).

fof(f126,plain,
    ( ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl6_6 ),
    inference(resolution,[],[f108,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f108,plain,
    ( v1_yellow_0(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f151,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f45,f148])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f146,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f44,f143])).

fof(f44,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f114,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f51,f111])).

fof(f51,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f109,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f50,f106])).

fof(f50,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f49,f101])).

fof(f49,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f48,f96])).

fof(f48,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f47,f91])).

fof(f47,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f89,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f46,f86])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f84,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f42,f81])).

fof(f42,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (30834)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (30859)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (30840)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (30850)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (30832)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (30833)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (30849)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (30835)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (30829)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (30831)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (30846)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (30828)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (30841)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (30853)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (30844)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (30848)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (30852)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (30838)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (30854)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (30855)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (30839)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (30856)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (30836)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (30858)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (30845)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (30843)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (30842)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (30851)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (30837)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (30850)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f617,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f109,f114,f146,f151,f156,f171,f216,f222,f227,f239,f266,f273,f313,f319,f447,f471,f538,f603,f611,f616])).
% 0.20/0.55  fof(f616,plain,(
% 0.20/0.55    ~spl6_12 | ~spl6_16 | ~spl6_22),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f615])).
% 0.20/0.55  fof(f615,plain,(
% 0.20/0.55    $false | (~spl6_12 | ~spl6_16 | ~spl6_22)),
% 0.20/0.55    inference(subsumption_resolution,[],[f614,f238])).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    ~v1_subset_1(sK1,sK1) | ~spl6_16),
% 0.20/0.55    inference(resolution,[],[f199,f79])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f71])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.55  fof(f199,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl6_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f197])).
% 0.20/0.55  fof(f197,plain,(
% 0.20/0.55    spl6_16 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.55  fof(f614,plain,(
% 0.20/0.55    v1_subset_1(sK1,sK1) | (~spl6_12 | ~spl6_22)),
% 0.20/0.55    inference(forward_demodulation,[],[f166,f256])).
% 0.20/0.55  fof(f256,plain,(
% 0.20/0.55    sK1 = u1_struct_0(sK0) | ~spl6_22),
% 0.20/0.55    inference(avatar_component_clause,[],[f254])).
% 0.20/0.55  fof(f254,plain,(
% 0.20/0.55    spl6_22 <=> sK1 = u1_struct_0(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_12),
% 0.20/0.55    inference(avatar_component_clause,[],[f164])).
% 0.20/0.55  fof(f164,plain,(
% 0.20/0.55    spl6_12 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.55  fof(f611,plain,(
% 0.20/0.55    spl6_1 | spl6_13 | ~spl6_35),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f610])).
% 0.20/0.55  fof(f610,plain,(
% 0.20/0.55    $false | (spl6_1 | spl6_13 | ~spl6_35)),
% 0.20/0.55    inference(subsumption_resolution,[],[f609,f170])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl6_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f168])).
% 0.20/0.55  fof(f168,plain,(
% 0.20/0.55    spl6_13 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.51/0.55  fof(f609,plain,(
% 1.51/0.55    r2_hidden(k3_yellow_0(sK0),sK1) | (spl6_1 | ~spl6_35)),
% 1.51/0.55    inference(resolution,[],[f602,f115])).
% 1.51/0.55  fof(f115,plain,(
% 1.51/0.55    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(X0,sK1)) ) | spl6_1),
% 1.51/0.55    inference(resolution,[],[f83,f67])).
% 1.51/0.55  fof(f67,plain,(
% 1.51/0.55    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f32])).
% 1.51/0.55  fof(f32,plain,(
% 1.51/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.51/0.55    inference(flattening,[],[f31])).
% 1.51/0.55  fof(f31,plain,(
% 1.51/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.51/0.55    inference(ennf_transformation,[],[f4])).
% 1.51/0.55  fof(f4,axiom,(
% 1.51/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.51/0.55  fof(f83,plain,(
% 1.51/0.55    ~v1_xboole_0(sK1) | spl6_1),
% 1.51/0.55    inference(avatar_component_clause,[],[f81])).
% 1.51/0.56  fof(f81,plain,(
% 1.51/0.56    spl6_1 <=> v1_xboole_0(sK1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.51/0.56  fof(f602,plain,(
% 1.51/0.56    m1_subset_1(k3_yellow_0(sK0),sK1) | ~spl6_35),
% 1.51/0.56    inference(avatar_component_clause,[],[f600])).
% 1.51/0.56  fof(f600,plain,(
% 1.51/0.56    spl6_35 <=> m1_subset_1(k3_yellow_0(sK0),sK1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.51/0.56  fof(f603,plain,(
% 1.51/0.56    spl6_35 | ~spl6_7 | ~spl6_22),
% 1.51/0.56    inference(avatar_split_clause,[],[f439,f254,f111,f600])).
% 1.51/0.56  fof(f111,plain,(
% 1.51/0.56    spl6_7 <=> l1_orders_2(sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.51/0.56  fof(f439,plain,(
% 1.51/0.56    m1_subset_1(k3_yellow_0(sK0),sK1) | (~spl6_7 | ~spl6_22)),
% 1.51/0.56    inference(subsumption_resolution,[],[f431,f113])).
% 1.51/0.56  fof(f113,plain,(
% 1.51/0.56    l1_orders_2(sK0) | ~spl6_7),
% 1.51/0.56    inference(avatar_component_clause,[],[f111])).
% 1.51/0.56  fof(f431,plain,(
% 1.51/0.56    m1_subset_1(k3_yellow_0(sK0),sK1) | ~l1_orders_2(sK0) | ~spl6_22),
% 1.51/0.56    inference(superposition,[],[f53,f256])).
% 1.51/0.56  fof(f53,plain,(
% 1.51/0.56    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f20])).
% 1.51/0.56  fof(f20,plain,(
% 1.51/0.56    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f10])).
% 1.51/0.56  fof(f10,axiom,(
% 1.51/0.56    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 1.51/0.56  fof(f538,plain,(
% 1.51/0.56    spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_19 | spl6_23 | ~spl6_24 | ~spl6_27),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f537])).
% 1.51/0.56  fof(f537,plain,(
% 1.51/0.56    $false | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_19 | spl6_23 | ~spl6_24 | ~spl6_27)),
% 1.51/0.56    inference(subsumption_resolution,[],[f532,f272])).
% 1.51/0.56  fof(f272,plain,(
% 1.51/0.56    m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl6_24),
% 1.51/0.56    inference(avatar_component_clause,[],[f270])).
% 1.51/0.56  fof(f270,plain,(
% 1.51/0.56    spl6_24 <=> m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.51/0.56  fof(f532,plain,(
% 1.51/0.56    ~m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_19 | spl6_23 | ~spl6_27)),
% 1.51/0.56    inference(resolution,[],[f528,f265])).
% 1.51/0.56  fof(f265,plain,(
% 1.51/0.56    ~r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1) | spl6_23),
% 1.51/0.56    inference(avatar_component_clause,[],[f263])).
% 1.51/0.56  fof(f263,plain,(
% 1.51/0.56    spl6_23 <=> r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.51/0.56  fof(f528,plain,(
% 1.51/0.56    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_19 | ~spl6_27)),
% 1.51/0.56    inference(subsumption_resolution,[],[f527,f169])).
% 1.51/0.56  fof(f169,plain,(
% 1.51/0.56    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl6_13),
% 1.51/0.56    inference(avatar_component_clause,[],[f168])).
% 1.51/0.56  fof(f527,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1)) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_19 | ~spl6_27)),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f526])).
% 1.51/0.56  fof(f526,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_19 | ~spl6_27)),
% 1.51/0.56    inference(resolution,[],[f524,f283])).
% 1.51/0.56  fof(f283,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r1_orders_2(sK0,X1,X0) | ~r2_hidden(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | (~spl6_7 | ~spl6_9 | ~spl6_10)),
% 1.51/0.56    inference(subsumption_resolution,[],[f282,f145])).
% 1.51/0.56  fof(f145,plain,(
% 1.51/0.56    v13_waybel_0(sK1,sK0) | ~spl6_9),
% 1.51/0.56    inference(avatar_component_clause,[],[f143])).
% 1.51/0.56  fof(f143,plain,(
% 1.51/0.56    spl6_9 <=> v13_waybel_0(sK1,sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.51/0.56  fof(f282,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,sK1) | ~r1_orders_2(sK0,X1,X0) | r2_hidden(X0,sK1) | ~v13_waybel_0(sK1,sK0)) ) | (~spl6_7 | ~spl6_10)),
% 1.51/0.56    inference(resolution,[],[f136,f150])).
% 1.51/0.56  fof(f150,plain,(
% 1.51/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_10),
% 1.51/0.56    inference(avatar_component_clause,[],[f148])).
% 1.51/0.56  fof(f148,plain,(
% 1.51/0.56    spl6_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.51/0.56  fof(f136,plain,(
% 1.51/0.56    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r2_hidden(X6,X5) | ~r1_orders_2(sK0,X6,X7) | r2_hidden(X7,X5) | ~v13_waybel_0(X5,sK0)) ) | ~spl6_7),
% 1.51/0.56    inference(subsumption_resolution,[],[f134,f77])).
% 1.51/0.56  fof(f77,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f38])).
% 1.51/0.56  fof(f38,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.51/0.56    inference(flattening,[],[f37])).
% 1.51/0.56  fof(f37,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.51/0.56    inference(ennf_transformation,[],[f6])).
% 1.51/0.56  fof(f6,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.51/0.56  fof(f134,plain,(
% 1.51/0.56    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r2_hidden(X6,X5) | ~r1_orders_2(sK0,X6,X7) | r2_hidden(X7,X5) | ~v13_waybel_0(X5,sK0)) ) | ~spl6_7),
% 1.51/0.56    inference(resolution,[],[f113,f59])).
% 1.51/0.56  fof(f59,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f23])).
% 1.51/0.56  fof(f23,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.51/0.56    inference(flattening,[],[f22])).
% 1.51/0.56  fof(f22,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f13])).
% 1.51/0.56  fof(f13,axiom,(
% 1.51/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.51/0.56  fof(f524,plain,(
% 1.51/0.56    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11 | ~spl6_19 | ~spl6_27)),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f523])).
% 1.51/0.56  fof(f523,plain,(
% 1.51/0.56    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11 | ~spl6_19 | ~spl6_27)),
% 1.51/0.56    inference(superposition,[],[f505,f125])).
% 1.51/0.56  fof(f125,plain,(
% 1.51/0.56    ( ! [X1] : (k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7)),
% 1.51/0.56    inference(subsumption_resolution,[],[f124,f113])).
% 1.51/0.56  fof(f124,plain,(
% 1.51/0.56    ( ! [X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.51/0.56    inference(subsumption_resolution,[],[f123,f103])).
% 1.51/0.56  fof(f103,plain,(
% 1.51/0.56    v5_orders_2(sK0) | ~spl6_5),
% 1.51/0.56    inference(avatar_component_clause,[],[f101])).
% 1.51/0.56  fof(f101,plain,(
% 1.51/0.56    spl6_5 <=> v5_orders_2(sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.51/0.56  fof(f123,plain,(
% 1.51/0.56    ( ! [X1] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.51/0.56    inference(subsumption_resolution,[],[f122,f88])).
% 1.51/0.56  fof(f88,plain,(
% 1.51/0.56    ~v2_struct_0(sK0) | spl6_2),
% 1.51/0.56    inference(avatar_component_clause,[],[f86])).
% 1.51/0.56  fof(f86,plain,(
% 1.51/0.56    spl6_2 <=> v2_struct_0(sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.51/0.56  fof(f122,plain,(
% 1.51/0.56    ( ! [X1] : (v2_struct_0(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1) ) | (~spl6_3 | ~spl6_4)),
% 1.51/0.56    inference(subsumption_resolution,[],[f117,f93])).
% 1.51/0.56  fof(f93,plain,(
% 1.51/0.56    v3_orders_2(sK0) | ~spl6_3),
% 1.51/0.56    inference(avatar_component_clause,[],[f91])).
% 1.51/0.56  fof(f91,plain,(
% 1.51/0.56    spl6_3 <=> v3_orders_2(sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.51/0.56  fof(f117,plain,(
% 1.51/0.56    ( ! [X1] : (~v3_orders_2(sK0) | v2_struct_0(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) = X1) ) | ~spl6_4),
% 1.51/0.56    inference(resolution,[],[f98,f63])).
% 1.51/0.56  fof(f63,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f27])).
% 1.51/0.56  fof(f27,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.51/0.56    inference(flattening,[],[f26])).
% 1.51/0.56  fof(f26,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f14])).
% 1.51/0.56  fof(f14,axiom,(
% 1.51/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).
% 1.51/0.56  fof(f98,plain,(
% 1.51/0.56    v4_orders_2(sK0) | ~spl6_4),
% 1.51/0.56    inference(avatar_component_clause,[],[f96])).
% 1.51/0.56  fof(f96,plain,(
% 1.51/0.56    spl6_4 <=> v4_orders_2(sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.51/0.56  fof(f505,plain,(
% 1.51/0.56    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,k5_waybel_0(sK0,X0))) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11 | ~spl6_19 | ~spl6_27)),
% 1.51/0.56    inference(resolution,[],[f472,f121])).
% 1.51/0.56  fof(f121,plain,(
% 1.51/0.56    ( ! [X0] : (r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7)),
% 1.51/0.56    inference(subsumption_resolution,[],[f120,f113])).
% 1.51/0.56  fof(f120,plain,(
% 1.51/0.56    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_yellow_0(sK0,k5_waybel_0(sK0,X0))) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.51/0.56    inference(subsumption_resolution,[],[f119,f103])).
% 1.51/0.56  fof(f119,plain,(
% 1.51/0.56    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_yellow_0(sK0,k5_waybel_0(sK0,X0))) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.51/0.56    inference(subsumption_resolution,[],[f118,f88])).
% 1.51/0.56  fof(f118,plain,(
% 1.51/0.56    ( ! [X0] : (v2_struct_0(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_yellow_0(sK0,k5_waybel_0(sK0,X0))) ) | (~spl6_3 | ~spl6_4)),
% 1.51/0.56    inference(subsumption_resolution,[],[f116,f93])).
% 1.51/0.56  fof(f116,plain,(
% 1.51/0.56    ( ! [X0] : (~v3_orders_2(sK0) | v2_struct_0(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_yellow_0(sK0,k5_waybel_0(sK0,X0))) ) | ~spl6_4),
% 1.51/0.56    inference(resolution,[],[f98,f62])).
% 1.51/0.56  fof(f62,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_yellow_0(X0,k5_waybel_0(X0,X1))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f27])).
% 1.51/0.56  fof(f472,plain,(
% 1.51/0.56    ( ! [X0] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))) ) | (~spl6_7 | ~spl6_11 | ~spl6_19 | ~spl6_27)),
% 1.51/0.56    inference(subsumption_resolution,[],[f284,f332])).
% 1.51/0.56  fof(f332,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_27),
% 1.51/0.56    inference(subsumption_resolution,[],[f325,f52])).
% 1.51/0.56  fof(f52,plain,(
% 1.51/0.56    v1_xboole_0(k1_xboole_0)),
% 1.51/0.56    inference(cnf_transformation,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    v1_xboole_0(k1_xboole_0)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.51/0.56  fof(f325,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)) ) | ~spl6_27),
% 1.51/0.56    inference(resolution,[],[f312,f78])).
% 1.51/0.56  fof(f78,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f39])).
% 1.51/0.56  fof(f39,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f7])).
% 1.51/0.56  fof(f7,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.51/0.56  fof(f312,plain,(
% 1.51/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl6_27),
% 1.51/0.56    inference(avatar_component_clause,[],[f310])).
% 1.51/0.56  fof(f310,plain,(
% 1.51/0.56    spl6_27 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.51/0.56  fof(f284,plain,(
% 1.51/0.56    ( ! [X0] : (r2_hidden(sK5(k1_xboole_0,X0),k1_xboole_0) | ~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))) ) | (~spl6_7 | ~spl6_11 | ~spl6_19)),
% 1.51/0.56    inference(resolution,[],[f279,f73])).
% 1.51/0.56  fof(f73,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f36])).
% 1.51/0.56  fof(f36,plain,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.56  fof(f279,plain,(
% 1.51/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) | ~r1_yellow_0(sK0,X0)) ) | (~spl6_7 | ~spl6_11 | ~spl6_19)),
% 1.51/0.56    inference(forward_demodulation,[],[f277,f226])).
% 1.51/0.56  fof(f226,plain,(
% 1.51/0.56    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl6_19),
% 1.51/0.56    inference(avatar_component_clause,[],[f224])).
% 1.51/0.56  fof(f224,plain,(
% 1.51/0.56    spl6_19 <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.51/0.56  fof(f277,plain,(
% 1.51/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))) ) | (~spl6_7 | ~spl6_11)),
% 1.51/0.56    inference(resolution,[],[f130,f155])).
% 1.51/0.56  fof(f155,plain,(
% 1.51/0.56    r1_yellow_0(sK0,k1_xboole_0) | ~spl6_11),
% 1.51/0.56    inference(avatar_component_clause,[],[f153])).
% 1.51/0.56  fof(f153,plain,(
% 1.51/0.56    spl6_11 <=> r1_yellow_0(sK0,k1_xboole_0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.51/0.56  fof(f130,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r1_yellow_0(sK0,X0) | ~r1_tarski(X0,X1) | ~r1_yellow_0(sK0,X1) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))) ) | ~spl6_7),
% 1.51/0.56    inference(resolution,[],[f113,f61])).
% 1.51/0.56  fof(f61,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_tarski(X1,X2) | ~r1_yellow_0(X0,X1) | ~r1_yellow_0(X0,X2) | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.51/0.56    inference(flattening,[],[f24])).
% 1.51/0.56  fof(f24,plain,(
% 1.51/0.56    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f11])).
% 1.51/0.56  fof(f11,axiom,(
% 1.51/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).
% 1.51/0.56  fof(f471,plain,(
% 1.51/0.56    spl6_25 | ~spl6_28),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f470])).
% 1.51/0.56  fof(f470,plain,(
% 1.51/0.56    $false | (spl6_25 | ~spl6_28)),
% 1.51/0.56    inference(subsumption_resolution,[],[f468,f294])).
% 1.51/0.56  fof(f294,plain,(
% 1.51/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl6_25),
% 1.51/0.56    inference(avatar_component_clause,[],[f293])).
% 1.51/0.56  fof(f293,plain,(
% 1.51/0.56    spl6_25 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.51/0.56  fof(f468,plain,(
% 1.51/0.56    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl6_28),
% 1.51/0.56    inference(resolution,[],[f318,f74])).
% 1.51/0.56  fof(f74,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f36])).
% 1.51/0.56  fof(f318,plain,(
% 1.51/0.56    r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl6_28),
% 1.51/0.56    inference(avatar_component_clause,[],[f316])).
% 1.51/0.56  fof(f316,plain,(
% 1.51/0.56    spl6_28 <=> r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.51/0.56  fof(f447,plain,(
% 1.51/0.56    spl6_13 | ~spl6_10 | spl6_22),
% 1.51/0.56    inference(avatar_split_clause,[],[f446,f254,f148,f168])).
% 1.51/0.56  fof(f446,plain,(
% 1.51/0.56    r2_hidden(k3_yellow_0(sK0),sK1) | (~spl6_10 | spl6_22)),
% 1.51/0.56    inference(subsumption_resolution,[],[f41,f445])).
% 1.51/0.56  fof(f445,plain,(
% 1.51/0.56    v1_subset_1(sK1,u1_struct_0(sK0)) | (~spl6_10 | spl6_22)),
% 1.51/0.56    inference(subsumption_resolution,[],[f207,f255])).
% 1.51/0.56  fof(f255,plain,(
% 1.51/0.56    sK1 != u1_struct_0(sK0) | spl6_22),
% 1.51/0.56    inference(avatar_component_clause,[],[f254])).
% 1.51/0.56  fof(f207,plain,(
% 1.51/0.56    sK1 = u1_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_10),
% 1.51/0.56    inference(resolution,[],[f150,f70])).
% 1.51/0.56  fof(f70,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f35])).
% 1.51/0.56  fof(f41,plain,(
% 1.51/0.56    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f19,plain,(
% 1.51/0.56    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.51/0.56    inference(flattening,[],[f18])).
% 1.51/0.56  fof(f18,plain,(
% 1.51/0.56    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f17])).
% 1.51/0.56  fof(f17,negated_conjecture,(
% 1.51/0.56    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.51/0.56    inference(negated_conjecture,[],[f16])).
% 1.51/0.56  fof(f16,conjecture,(
% 1.51/0.56    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.51/0.56  fof(f319,plain,(
% 1.51/0.56    spl6_28 | spl6_25),
% 1.51/0.56    inference(avatar_split_clause,[],[f314,f293,f316])).
% 1.51/0.56  fof(f314,plain,(
% 1.51/0.56    r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl6_25),
% 1.51/0.56    inference(resolution,[],[f294,f73])).
% 1.51/0.56  fof(f313,plain,(
% 1.51/0.56    spl6_27 | ~spl6_25),
% 1.51/0.56    inference(avatar_split_clause,[],[f302,f293,f310])).
% 1.51/0.56  fof(f302,plain,(
% 1.51/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl6_25),
% 1.51/0.56    inference(resolution,[],[f295,f75])).
% 1.51/0.56  fof(f75,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f5])).
% 1.51/0.56  fof(f5,axiom,(
% 1.51/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.51/0.56  fof(f295,plain,(
% 1.51/0.56    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl6_25),
% 1.51/0.56    inference(avatar_component_clause,[],[f293])).
% 1.51/0.56  fof(f273,plain,(
% 1.51/0.56    spl6_22 | spl6_24 | ~spl6_10),
% 1.51/0.56    inference(avatar_split_clause,[],[f161,f148,f270,f254])).
% 1.51/0.56  fof(f161,plain,(
% 1.51/0.56    m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~spl6_10),
% 1.51/0.56    inference(resolution,[],[f150,f68])).
% 1.51/0.56  fof(f68,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK4(X0,X1),X0) | X0 = X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f34])).
% 1.51/0.56  fof(f34,plain,(
% 1.51/0.56    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.56    inference(flattening,[],[f33])).
% 1.51/0.56  fof(f33,plain,(
% 1.51/0.56    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f3])).
% 1.51/0.56  fof(f3,axiom,(
% 1.51/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 1.51/0.56  fof(f266,plain,(
% 1.51/0.56    spl6_22 | ~spl6_23 | ~spl6_10),
% 1.51/0.56    inference(avatar_split_clause,[],[f162,f148,f263,f254])).
% 1.51/0.56  fof(f162,plain,(
% 1.51/0.56    ~r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0) | ~spl6_10),
% 1.51/0.56    inference(resolution,[],[f150,f69])).
% 1.51/0.56  fof(f69,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK4(X0,X1),X1) | X0 = X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f34])).
% 1.51/0.56  fof(f239,plain,(
% 1.51/0.56    spl6_15 | ~spl6_18),
% 1.51/0.56    inference(avatar_split_clause,[],[f228,f219,f192])).
% 1.51/0.56  fof(f192,plain,(
% 1.51/0.56    spl6_15 <=> r1_tarski(sK1,sK1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.51/0.56  fof(f219,plain,(
% 1.51/0.56    spl6_18 <=> r2_hidden(sK5(sK1,sK1),sK1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.51/0.56  fof(f228,plain,(
% 1.51/0.56    r1_tarski(sK1,sK1) | ~spl6_18),
% 1.51/0.56    inference(resolution,[],[f221,f74])).
% 1.51/0.56  fof(f221,plain,(
% 1.51/0.56    r2_hidden(sK5(sK1,sK1),sK1) | ~spl6_18),
% 1.51/0.56    inference(avatar_component_clause,[],[f219])).
% 1.51/0.56  fof(f227,plain,(
% 1.51/0.56    spl6_19 | ~spl6_7),
% 1.51/0.56    inference(avatar_split_clause,[],[f135,f111,f224])).
% 1.51/0.56  fof(f135,plain,(
% 1.51/0.56    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl6_7),
% 1.51/0.56    inference(resolution,[],[f113,f54])).
% 1.51/0.56  fof(f54,plain,(
% 1.51/0.56    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f21])).
% 1.51/0.56  fof(f21,plain,(
% 1.51/0.56    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f8])).
% 1.51/0.56  fof(f8,axiom,(
% 1.51/0.56    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.51/0.56  fof(f222,plain,(
% 1.51/0.56    spl6_18 | spl6_15),
% 1.51/0.56    inference(avatar_split_clause,[],[f217,f192,f219])).
% 1.51/0.56  fof(f217,plain,(
% 1.51/0.56    r2_hidden(sK5(sK1,sK1),sK1) | spl6_15),
% 1.51/0.56    inference(resolution,[],[f193,f73])).
% 1.51/0.56  fof(f193,plain,(
% 1.51/0.56    ~r1_tarski(sK1,sK1) | spl6_15),
% 1.51/0.56    inference(avatar_component_clause,[],[f192])).
% 1.51/0.56  fof(f216,plain,(
% 1.51/0.56    spl6_16 | ~spl6_15),
% 1.51/0.56    inference(avatar_split_clause,[],[f202,f192,f197])).
% 1.51/0.56  fof(f202,plain,(
% 1.51/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl6_15),
% 1.51/0.56    inference(resolution,[],[f194,f75])).
% 1.51/0.56  fof(f194,plain,(
% 1.51/0.56    r1_tarski(sK1,sK1) | ~spl6_15),
% 1.51/0.56    inference(avatar_component_clause,[],[f192])).
% 1.51/0.56  fof(f171,plain,(
% 1.51/0.56    spl6_12 | ~spl6_13),
% 1.51/0.56    inference(avatar_split_clause,[],[f40,f168,f164])).
% 1.51/0.56  fof(f40,plain,(
% 1.51/0.56    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f156,plain,(
% 1.51/0.56    spl6_11 | spl6_2 | ~spl6_5 | ~spl6_6 | ~spl6_7),
% 1.51/0.56    inference(avatar_split_clause,[],[f129,f111,f106,f101,f86,f153])).
% 1.51/0.56  fof(f106,plain,(
% 1.51/0.56    spl6_6 <=> v1_yellow_0(sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.51/0.56  fof(f129,plain,(
% 1.51/0.56    r1_yellow_0(sK0,k1_xboole_0) | (spl6_2 | ~spl6_5 | ~spl6_6 | ~spl6_7)),
% 1.51/0.56    inference(subsumption_resolution,[],[f128,f113])).
% 1.51/0.56  fof(f128,plain,(
% 1.51/0.56    ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0) | (spl6_2 | ~spl6_5 | ~spl6_6)),
% 1.51/0.56    inference(subsumption_resolution,[],[f127,f88])).
% 1.51/0.56  fof(f127,plain,(
% 1.51/0.56    v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0) | (~spl6_5 | ~spl6_6)),
% 1.51/0.56    inference(subsumption_resolution,[],[f126,f103])).
% 1.51/0.56  fof(f126,plain,(
% 1.51/0.56    ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0) | ~spl6_6),
% 1.51/0.56    inference(resolution,[],[f108,f64])).
% 1.51/0.56  fof(f64,plain,(
% 1.51/0.56    ( ! [X0] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | r1_yellow_0(X0,k1_xboole_0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f29])).
% 1.51/0.56  fof(f29,plain,(
% 1.51/0.56    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.51/0.56    inference(flattening,[],[f28])).
% 1.51/0.56  fof(f28,plain,(
% 1.51/0.56    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f12])).
% 1.51/0.56  fof(f12,axiom,(
% 1.51/0.56    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 1.51/0.56  fof(f108,plain,(
% 1.51/0.56    v1_yellow_0(sK0) | ~spl6_6),
% 1.51/0.56    inference(avatar_component_clause,[],[f106])).
% 1.51/0.56  fof(f151,plain,(
% 1.51/0.56    spl6_10),
% 1.51/0.56    inference(avatar_split_clause,[],[f45,f148])).
% 1.51/0.56  fof(f45,plain,(
% 1.51/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f146,plain,(
% 1.51/0.56    spl6_9),
% 1.51/0.56    inference(avatar_split_clause,[],[f44,f143])).
% 1.51/0.56  fof(f44,plain,(
% 1.51/0.56    v13_waybel_0(sK1,sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f114,plain,(
% 1.51/0.56    spl6_7),
% 1.51/0.56    inference(avatar_split_clause,[],[f51,f111])).
% 1.51/0.56  fof(f51,plain,(
% 1.51/0.56    l1_orders_2(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f109,plain,(
% 1.51/0.56    spl6_6),
% 1.51/0.56    inference(avatar_split_clause,[],[f50,f106])).
% 1.51/0.56  fof(f50,plain,(
% 1.51/0.56    v1_yellow_0(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f104,plain,(
% 1.51/0.56    spl6_5),
% 1.51/0.56    inference(avatar_split_clause,[],[f49,f101])).
% 1.51/0.56  fof(f49,plain,(
% 1.51/0.56    v5_orders_2(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f99,plain,(
% 1.51/0.56    spl6_4),
% 1.51/0.56    inference(avatar_split_clause,[],[f48,f96])).
% 1.51/0.56  fof(f48,plain,(
% 1.51/0.56    v4_orders_2(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f94,plain,(
% 1.51/0.56    spl6_3),
% 1.51/0.56    inference(avatar_split_clause,[],[f47,f91])).
% 1.51/0.56  fof(f47,plain,(
% 1.51/0.56    v3_orders_2(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f89,plain,(
% 1.51/0.56    ~spl6_2),
% 1.51/0.56    inference(avatar_split_clause,[],[f46,f86])).
% 1.51/0.56  fof(f46,plain,(
% 1.51/0.56    ~v2_struct_0(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f84,plain,(
% 1.51/0.56    ~spl6_1),
% 1.51/0.56    inference(avatar_split_clause,[],[f42,f81])).
% 1.51/0.56  fof(f42,plain,(
% 1.51/0.56    ~v1_xboole_0(sK1)),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  % SZS output end Proof for theBenchmark
% 1.51/0.56  % (30850)------------------------------
% 1.51/0.56  % (30850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (30850)Termination reason: Refutation
% 1.51/0.56  
% 1.51/0.56  % (30850)Memory used [KB]: 11129
% 1.51/0.56  % (30850)Time elapsed: 0.142 s
% 1.51/0.56  % (30850)------------------------------
% 1.51/0.56  % (30850)------------------------------
% 1.51/0.56  % (30825)Success in time 0.204 s
%------------------------------------------------------------------------------
