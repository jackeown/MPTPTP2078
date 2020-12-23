%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1731+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:31 EST 2020

% Result     : Theorem 2.90s
% Output     : Refutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 545 expanded)
%              Number of leaves         :   28 ( 248 expanded)
%              Depth                    :    8
%              Number of atoms          :  958 (4921 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5833,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5163,f5168,f5173,f5178,f5183,f5188,f5193,f5198,f5203,f5220,f5241,f5249,f5251,f5288,f5324,f5398,f5422,f5707,f5711,f5726,f5756,f5758,f5817,f5819,f5832])).

fof(f5832,plain,
    ( spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | spl200_10
    | ~ spl200_11
    | ~ spl200_15 ),
    inference(avatar_contradiction_clause,[],[f5831])).

fof(f5831,plain,
    ( $false
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | spl200_10
    | ~ spl200_11
    | ~ spl200_15 ),
    inference(subsumption_resolution,[],[f5830,f5206])).

fof(f5206,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | spl200_10 ),
    inference(avatar_component_clause,[],[f5205])).

fof(f5205,plain,
    ( spl200_10
  <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_10])])).

fof(f5830,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_11
    | ~ spl200_15 ),
    inference(forward_demodulation,[],[f5821,f5373])).

fof(f5373,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | spl200_1
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | ~ spl200_7
    | ~ spl200_8 ),
    inference(unit_resulting_resolution,[],[f5162,f5172,f5177,f5192,f5182,f5197,f4161])).

fof(f4161,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3417])).

fof(f3417,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3416])).

fof(f3416,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3324])).

fof(f3324,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f5197,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl200_8 ),
    inference(avatar_component_clause,[],[f5195])).

fof(f5195,plain,
    ( spl200_8
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_8])])).

fof(f5182,plain,
    ( ~ v2_struct_0(sK2)
    | spl200_5 ),
    inference(avatar_component_clause,[],[f5180])).

fof(f5180,plain,
    ( spl200_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_5])])).

fof(f5192,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl200_7 ),
    inference(avatar_component_clause,[],[f5190])).

fof(f5190,plain,
    ( spl200_7
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_7])])).

fof(f5177,plain,
    ( ~ v2_struct_0(sK1)
    | spl200_4 ),
    inference(avatar_component_clause,[],[f5175])).

fof(f5175,plain,
    ( spl200_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_4])])).

fof(f5172,plain,
    ( l1_pre_topc(sK0)
    | ~ spl200_3 ),
    inference(avatar_component_clause,[],[f5170])).

fof(f5170,plain,
    ( spl200_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_3])])).

fof(f5162,plain,
    ( ~ v2_struct_0(sK0)
    | spl200_1 ),
    inference(avatar_component_clause,[],[f5160])).

fof(f5160,plain,
    ( spl200_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_1])])).

fof(f5821,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK2,sK1),sK3)
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_11
    | ~ spl200_15 ),
    inference(unit_resulting_resolution,[],[f5162,f5167,f5172,f5182,f5187,f5177,f5197,f5192,f5202,f5229,f5211,f4145])).

fof(f4145,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tsep_1(X1,X3)
      | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3408])).

fof(f3408,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      | ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1)
                      | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) )
                    & ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(X1,X3)
                      | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3407])).

fof(f3407,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      | ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1)
                      | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) )
                    & ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(X1,X3)
                      | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3379])).

fof(f3379,axiom,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & ~ ( r1_tsep_1(X3,X2)
                            & r1_tsep_1(X3,X1) ) )
                    & ~ ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1)
                        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & ~ ( r1_tsep_1(X2,X3)
                            & r1_tsep_1(X1,X3) ) )
                    & ~ ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3)
                        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tmap_1)).

fof(f5211,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl200_11 ),
    inference(avatar_component_clause,[],[f5209])).

fof(f5209,plain,
    ( spl200_11
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_11])])).

fof(f5229,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl200_15 ),
    inference(avatar_component_clause,[],[f5227])).

fof(f5227,plain,
    ( spl200_15
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_15])])).

fof(f5202,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl200_9 ),
    inference(avatar_component_clause,[],[f5200])).

fof(f5200,plain,
    ( spl200_9
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_9])])).

fof(f5187,plain,
    ( ~ v2_struct_0(sK3)
    | spl200_6 ),
    inference(avatar_component_clause,[],[f5185])).

fof(f5185,plain,
    ( spl200_6
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_6])])).

fof(f5167,plain,
    ( v2_pre_topc(sK0)
    | ~ spl200_2 ),
    inference(avatar_component_clause,[],[f5165])).

fof(f5165,plain,
    ( spl200_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_2])])).

fof(f5819,plain,
    ( spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_10
    | spl200_11 ),
    inference(avatar_contradiction_clause,[],[f5818])).

fof(f5818,plain,
    ( $false
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_10
    | spl200_11 ),
    inference(subsumption_resolution,[],[f5210,f5764])).

fof(f5764,plain,
    ( r1_tsep_1(sK1,sK3)
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_10 ),
    inference(unit_resulting_resolution,[],[f5162,f5167,f5172,f5177,f5187,f5182,f5192,f5197,f5202,f5207,f4146])).

fof(f4146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3408])).

fof(f5207,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl200_10 ),
    inference(avatar_component_clause,[],[f5205])).

fof(f5210,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl200_11 ),
    inference(avatar_component_clause,[],[f5209])).

fof(f5817,plain,
    ( spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | spl200_12
    | ~ spl200_13
    | ~ spl200_16 ),
    inference(avatar_contradiction_clause,[],[f5816])).

fof(f5816,plain,
    ( $false
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | spl200_12
    | ~ spl200_13
    | ~ spl200_16 ),
    inference(subsumption_resolution,[],[f5775,f5214])).

fof(f5214,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | spl200_12 ),
    inference(avatar_component_clause,[],[f5213])).

fof(f5213,plain,
    ( spl200_12
  <=> r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_12])])).

fof(f5775,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_13
    | ~ spl200_16 ),
    inference(unit_resulting_resolution,[],[f5162,f5182,f5172,f5177,f5167,f5234,f5197,f5187,f5192,f5202,f5219,f4148])).

fof(f4148,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tsep_1(X3,X1)
      | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X3,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3408])).

fof(f5219,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl200_13 ),
    inference(avatar_component_clause,[],[f5217])).

fof(f5217,plain,
    ( spl200_13
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_13])])).

fof(f5234,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl200_16 ),
    inference(avatar_component_clause,[],[f5232])).

fof(f5232,plain,
    ( spl200_16
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_16])])).

fof(f5758,plain,
    ( spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_10
    | spl200_15 ),
    inference(avatar_contradiction_clause,[],[f5757])).

fof(f5757,plain,
    ( $false
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_10
    | spl200_15 ),
    inference(subsumption_resolution,[],[f5207,f5747])).

fof(f5747,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | spl200_15 ),
    inference(forward_demodulation,[],[f5734,f5373])).

fof(f5734,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK2,sK1),sK3)
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | spl200_15 ),
    inference(unit_resulting_resolution,[],[f5162,f5167,f5172,f5182,f5187,f5177,f5192,f5197,f5202,f5228,f4146])).

fof(f5228,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | spl200_15 ),
    inference(avatar_component_clause,[],[f5227])).

fof(f5756,plain,
    ( spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_5
    | spl200_6
    | ~ spl200_8
    | ~ spl200_9
    | spl200_15
    | ~ spl200_16
    | ~ spl200_24 ),
    inference(avatar_contradiction_clause,[],[f5755])).

fof(f5755,plain,
    ( $false
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_5
    | spl200_6
    | ~ spl200_8
    | ~ spl200_9
    | spl200_15
    | ~ spl200_16
    | ~ spl200_24 ),
    inference(subsumption_resolution,[],[f5749,f5416])).

fof(f5416,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ spl200_24 ),
    inference(unit_resulting_resolution,[],[f5397,f4193])).

fof(f4193,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3449])).

fof(f3449,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3367])).

fof(f3367,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f5397,plain,
    ( l1_pre_topc(sK3)
    | ~ spl200_24 ),
    inference(avatar_component_clause,[],[f5395])).

fof(f5395,plain,
    ( spl200_24
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_24])])).

fof(f5749,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_5
    | spl200_6
    | ~ spl200_8
    | ~ spl200_9
    | spl200_15
    | ~ spl200_16 ),
    inference(unit_resulting_resolution,[],[f5162,f5167,f5172,f5187,f5182,f5187,f5202,f5202,f5197,f5228,f5234,f4138])).

fof(f4138,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3404])).

fof(f3404,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3403])).

fof(f3403,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3358])).

fof(f3358,axiom,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f5726,plain,
    ( spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_5
    | spl200_6
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_15
    | spl200_16
    | ~ spl200_23 ),
    inference(avatar_contradiction_clause,[],[f5725])).

fof(f5725,plain,
    ( $false
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_5
    | spl200_6
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_15
    | spl200_16
    | ~ spl200_23 ),
    inference(subsumption_resolution,[],[f5719,f5356])).

fof(f5356,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ spl200_23 ),
    inference(unit_resulting_resolution,[],[f5323,f4193])).

fof(f5323,plain,
    ( l1_pre_topc(sK2)
    | ~ spl200_23 ),
    inference(avatar_component_clause,[],[f5321])).

fof(f5321,plain,
    ( spl200_23
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_23])])).

fof(f5719,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_5
    | spl200_6
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_15
    | spl200_16 ),
    inference(unit_resulting_resolution,[],[f5162,f5167,f5172,f5182,f5187,f5182,f5197,f5197,f5202,f5233,f5229,f4138])).

fof(f5233,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | spl200_16 ),
    inference(avatar_component_clause,[],[f5232])).

fof(f5711,plain,
    ( spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_12
    | spl200_13 ),
    inference(avatar_contradiction_clause,[],[f5710])).

fof(f5710,plain,
    ( $false
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_12
    | spl200_13 ),
    inference(subsumption_resolution,[],[f5666,f5215])).

fof(f5215,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl200_12 ),
    inference(avatar_component_clause,[],[f5213])).

fof(f5666,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | spl200_13 ),
    inference(unit_resulting_resolution,[],[f5162,f5167,f5172,f5177,f5187,f5182,f5197,f5192,f5202,f5218,f4149])).

fof(f4149,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3408])).

fof(f5218,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl200_13 ),
    inference(avatar_component_clause,[],[f5217])).

fof(f5707,plain,
    ( spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_12
    | spl200_16 ),
    inference(avatar_contradiction_clause,[],[f5706])).

fof(f5706,plain,
    ( $false
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | ~ spl200_12
    | spl200_16 ),
    inference(subsumption_resolution,[],[f5705,f5215])).

fof(f5705,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | spl200_16 ),
    inference(forward_demodulation,[],[f5669,f5373])).

fof(f5669,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK1))
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_5
    | spl200_6
    | ~ spl200_7
    | ~ spl200_8
    | ~ spl200_9
    | spl200_16 ),
    inference(unit_resulting_resolution,[],[f5162,f5167,f5172,f5182,f5187,f5177,f5192,f5197,f5202,f5233,f4149])).

fof(f5422,plain,
    ( spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_6
    | ~ spl200_7
    | ~ spl200_9
    | ~ spl200_11
    | spl200_13
    | ~ spl200_22 ),
    inference(avatar_contradiction_clause,[],[f5421])).

fof(f5421,plain,
    ( $false
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_6
    | ~ spl200_7
    | ~ spl200_9
    | ~ spl200_11
    | spl200_13
    | ~ spl200_22 ),
    inference(subsumption_resolution,[],[f5419,f5299])).

fof(f5299,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ spl200_22 ),
    inference(unit_resulting_resolution,[],[f5287,f4193])).

fof(f5287,plain,
    ( l1_pre_topc(sK1)
    | ~ spl200_22 ),
    inference(avatar_component_clause,[],[f5285])).

fof(f5285,plain,
    ( spl200_22
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl200_22])])).

fof(f5419,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | spl200_1
    | ~ spl200_2
    | ~ spl200_3
    | spl200_4
    | spl200_6
    | ~ spl200_7
    | ~ spl200_9
    | ~ spl200_11
    | spl200_13 ),
    inference(unit_resulting_resolution,[],[f5162,f5177,f5172,f5177,f5211,f5192,f5187,f5192,f5218,f5202,f5167,f4138])).

fof(f5398,plain,
    ( spl200_24
    | ~ spl200_3
    | ~ spl200_9 ),
    inference(avatar_split_clause,[],[f5265,f5200,f5170,f5395])).

fof(f5265,plain,
    ( l1_pre_topc(sK3)
    | ~ spl200_3
    | ~ spl200_9 ),
    inference(unit_resulting_resolution,[],[f5202,f5172,f4192])).

fof(f4192,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3448])).

fof(f3448,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f5324,plain,
    ( spl200_23
    | ~ spl200_3
    | ~ spl200_8 ),
    inference(avatar_split_clause,[],[f5264,f5195,f5170,f5321])).

fof(f5264,plain,
    ( l1_pre_topc(sK2)
    | ~ spl200_3
    | ~ spl200_8 ),
    inference(unit_resulting_resolution,[],[f5197,f5172,f4192])).

fof(f5288,plain,
    ( spl200_22
    | ~ spl200_3
    | ~ spl200_7 ),
    inference(avatar_split_clause,[],[f5263,f5190,f5170,f5285])).

fof(f5263,plain,
    ( l1_pre_topc(sK1)
    | ~ spl200_3
    | ~ spl200_7 ),
    inference(unit_resulting_resolution,[],[f5192,f5172,f4192])).

fof(f5251,plain,
    ( ~ spl200_11
    | ~ spl200_15
    | ~ spl200_10
    | ~ spl200_13
    | ~ spl200_16
    | ~ spl200_12 ),
    inference(avatar_split_clause,[],[f4135,f5213,f5232,f5217,f5205,f5227,f5209])).

fof(f4135,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK3,sK2)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f3822])).

fof(f3822,plain,
    ( ( ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
        & r1_tsep_1(sK3,sK2)
        & r1_tsep_1(sK3,sK1) )
      | ( ( ~ r1_tsep_1(sK3,sK2)
          | ~ r1_tsep_1(sK3,sK1) )
        & r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) )
      | ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
        & r1_tsep_1(sK2,sK3)
        & r1_tsep_1(sK1,sK3) )
      | ( ( ~ r1_tsep_1(sK2,sK3)
          | ~ r1_tsep_1(sK1,sK3) )
        & r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ) )
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3400,f3821,f3820,f3819,f3818])).

fof(f3818,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) )
                      | ( ( ~ r1_tsep_1(X3,X2)
                          | ~ r1_tsep_1(X3,X1) )
                        & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) )
                      | ( ( ~ r1_tsep_1(X2,X3)
                          | ~ r1_tsep_1(X1,X3) )
                        & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3819,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2))
                    & r1_tsep_1(X3,X2)
                    & r1_tsep_1(X3,X1) )
                  | ( ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1) )
                    & r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2)) )
                  | ( ~ r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3)
                    & r1_tsep_1(X2,X3)
                    & r1_tsep_1(X1,X3) )
                  | ( ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(X1,X3) )
                    & r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3) ) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(sK0,sK1,X2))
                  & r1_tsep_1(X3,X2)
                  & r1_tsep_1(X3,sK1) )
                | ( ( ~ r1_tsep_1(X3,X2)
                    | ~ r1_tsep_1(X3,sK1) )
                  & r1_tsep_1(X3,k1_tsep_1(sK0,sK1,X2)) )
                | ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,X2),X3)
                  & r1_tsep_1(X2,X3)
                  & r1_tsep_1(sK1,X3) )
                | ( ( ~ r1_tsep_1(X2,X3)
                    | ~ r1_tsep_1(sK1,X3) )
                  & r1_tsep_1(k1_tsep_1(sK0,sK1,X2),X3) ) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3820,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(sK0,sK1,X2))
                & r1_tsep_1(X3,X2)
                & r1_tsep_1(X3,sK1) )
              | ( ( ~ r1_tsep_1(X3,X2)
                  | ~ r1_tsep_1(X3,sK1) )
                & r1_tsep_1(X3,k1_tsep_1(sK0,sK1,X2)) )
              | ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,X2),X3)
                & r1_tsep_1(X2,X3)
                & r1_tsep_1(sK1,X3) )
              | ( ( ~ r1_tsep_1(X2,X3)
                  | ~ r1_tsep_1(sK1,X3) )
                & r1_tsep_1(k1_tsep_1(sK0,sK1,X2),X3) ) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK2))
              & r1_tsep_1(X3,sK2)
              & r1_tsep_1(X3,sK1) )
            | ( ( ~ r1_tsep_1(X3,sK2)
                | ~ r1_tsep_1(X3,sK1) )
              & r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK2)) )
            | ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),X3)
              & r1_tsep_1(sK2,X3)
              & r1_tsep_1(sK1,X3) )
            | ( ( ~ r1_tsep_1(sK2,X3)
                | ~ r1_tsep_1(sK1,X3) )
              & r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),X3) ) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3821,plain,
    ( ? [X3] :
        ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK2))
            & r1_tsep_1(X3,sK2)
            & r1_tsep_1(X3,sK1) )
          | ( ( ~ r1_tsep_1(X3,sK2)
              | ~ r1_tsep_1(X3,sK1) )
            & r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK2)) )
          | ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),X3)
            & r1_tsep_1(sK2,X3)
            & r1_tsep_1(sK1,X3) )
          | ( ( ~ r1_tsep_1(sK2,X3)
              | ~ r1_tsep_1(sK1,X3) )
            & r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),X3) ) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
          & r1_tsep_1(sK3,sK2)
          & r1_tsep_1(sK3,sK1) )
        | ( ( ~ r1_tsep_1(sK3,sK2)
            | ~ r1_tsep_1(sK3,sK1) )
          & r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) )
        | ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
          & r1_tsep_1(sK2,sK3)
          & r1_tsep_1(sK1,sK3) )
        | ( ( ~ r1_tsep_1(sK2,sK3)
            | ~ r1_tsep_1(sK1,sK3) )
          & r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3400,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3399])).

fof(f3399,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3381])).

fof(f3381,negated_conjecture,(
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
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) )
                       => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                       => ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) ) )
                      & ( ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) )
                       => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                      & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                       => ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3380])).

fof(f3380,conjecture,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) )
                     => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                     => ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) )
                     => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                    & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                     => ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tmap_1)).

fof(f5249,plain,
    ( spl200_10
    | spl200_11
    | ~ spl200_13
    | ~ spl200_16
    | ~ spl200_12 ),
    inference(avatar_split_clause,[],[f4130,f5213,f5232,f5217,f5209,f5205])).

fof(f4130,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK3,sK2)
    | ~ r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK1,sK3)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f3822])).

fof(f5241,plain,
    ( spl200_10
    | spl200_15
    | spl200_12
    | spl200_16 ),
    inference(avatar_split_clause,[],[f4114,f5232,f5213,f5227,f5205])).

fof(f4114,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f3822])).

fof(f5220,plain,
    ( spl200_10
    | spl200_11
    | spl200_12
    | spl200_13 ),
    inference(avatar_split_clause,[],[f4100,f5217,f5213,f5209,f5205])).

fof(f4100,plain,
    ( r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK1,sK3)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f3822])).

fof(f5203,plain,(
    spl200_9 ),
    inference(avatar_split_clause,[],[f4099,f5200])).

fof(f4099,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f3822])).

fof(f5198,plain,(
    spl200_8 ),
    inference(avatar_split_clause,[],[f4097,f5195])).

fof(f4097,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3822])).

fof(f5193,plain,(
    spl200_7 ),
    inference(avatar_split_clause,[],[f4095,f5190])).

fof(f4095,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3822])).

fof(f5188,plain,(
    ~ spl200_6 ),
    inference(avatar_split_clause,[],[f4098,f5185])).

fof(f4098,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3822])).

fof(f5183,plain,(
    ~ spl200_5 ),
    inference(avatar_split_clause,[],[f4096,f5180])).

fof(f4096,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3822])).

fof(f5178,plain,(
    ~ spl200_4 ),
    inference(avatar_split_clause,[],[f4094,f5175])).

fof(f4094,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3822])).

fof(f5173,plain,(
    spl200_3 ),
    inference(avatar_split_clause,[],[f4093,f5170])).

fof(f4093,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3822])).

fof(f5168,plain,(
    spl200_2 ),
    inference(avatar_split_clause,[],[f4092,f5165])).

fof(f4092,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3822])).

fof(f5163,plain,(
    ~ spl200_1 ),
    inference(avatar_split_clause,[],[f4091,f5160])).

fof(f4091,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3822])).
%------------------------------------------------------------------------------
