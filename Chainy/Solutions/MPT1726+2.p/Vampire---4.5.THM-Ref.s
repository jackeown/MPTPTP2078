%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1726+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:30 EST 2020

% Result     : Theorem 20.10s
% Output     : Refutation 20.10s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 546 expanded)
%              Number of leaves         :   35 ( 276 expanded)
%              Depth                    :    7
%              Number of atoms          :  909 (4569 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30219,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5574,f5579,f5584,f5589,f5594,f5599,f5604,f5609,f5614,f5619,f5624,f5629,f5634,f5643,f5657,f6301,f9930,f10050,f10904,f12396,f24715,f25819,f25913,f29955,f30073])).

fof(f30073,plain,
    ( spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_5
    | spl225_6
    | spl225_7
    | ~ spl225_9
    | ~ spl225_10
    | ~ spl225_11
    | ~ spl225_13
    | spl225_14
    | ~ spl225_18
    | spl225_85
    | spl225_109
    | ~ spl225_140
    | ~ spl225_160
    | ~ spl225_176 ),
    inference(avatar_contradiction_clause,[],[f30072])).

fof(f30072,plain,
    ( $false
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_5
    | spl225_6
    | spl225_7
    | ~ spl225_9
    | ~ spl225_10
    | ~ spl225_11
    | ~ spl225_13
    | spl225_14
    | ~ spl225_18
    | spl225_85
    | spl225_109
    | ~ spl225_140
    | ~ spl225_160
    | ~ spl225_176 ),
    inference(subsumption_resolution,[],[f30068,f26097])).

fof(f26097,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_5
    | spl225_6
    | spl225_7
    | ~ spl225_9
    | ~ spl225_10
    | ~ spl225_11
    | ~ spl225_13
    | spl225_14 ),
    inference(unit_resulting_resolution,[],[f5573,f5603,f5583,f5593,f5633,f5623,f5598,f5578,f5613,f5618,f5638,f4349])).

fof(f4349,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3434])).

fof(f3434,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      | ~ m1_pre_topc(X2,X3) )
                    & ( ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3433])).

fof(f3433,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      | ~ m1_pre_topc(X2,X3) )
                    & ( ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3374])).

fof(f3374,axiom,(
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
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                      & ( m1_pre_topc(X1,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tmap_1)).

fof(f5638,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | spl225_14 ),
    inference(avatar_component_clause,[],[f5636])).

fof(f5636,plain,
    ( spl225_14
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_14])])).

fof(f5618,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl225_10 ),
    inference(avatar_component_clause,[],[f5616])).

fof(f5616,plain,
    ( spl225_10
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_10])])).

fof(f5613,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl225_9 ),
    inference(avatar_component_clause,[],[f5611])).

fof(f5611,plain,
    ( spl225_9
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_9])])).

fof(f5578,plain,
    ( v2_pre_topc(sK0)
    | ~ spl225_2 ),
    inference(avatar_component_clause,[],[f5576])).

fof(f5576,plain,
    ( spl225_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_2])])).

fof(f5598,plain,
    ( ~ v2_struct_0(sK3)
    | spl225_6 ),
    inference(avatar_component_clause,[],[f5596])).

fof(f5596,plain,
    ( spl225_6
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_6])])).

fof(f5623,plain,
    ( m1_pre_topc(sK4,sK0)
    | ~ spl225_11 ),
    inference(avatar_component_clause,[],[f5621])).

fof(f5621,plain,
    ( spl225_11
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_11])])).

fof(f5633,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl225_13 ),
    inference(avatar_component_clause,[],[f5631])).

fof(f5631,plain,
    ( spl225_13
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_13])])).

fof(f5593,plain,
    ( ~ v2_struct_0(sK2)
    | spl225_5 ),
    inference(avatar_component_clause,[],[f5591])).

fof(f5591,plain,
    ( spl225_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_5])])).

fof(f5583,plain,
    ( l1_pre_topc(sK0)
    | ~ spl225_3 ),
    inference(avatar_component_clause,[],[f5581])).

fof(f5581,plain,
    ( spl225_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_3])])).

fof(f5603,plain,
    ( ~ v2_struct_0(sK4)
    | spl225_7 ),
    inference(avatar_component_clause,[],[f5601])).

fof(f5601,plain,
    ( spl225_7
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_7])])).

fof(f5573,plain,
    ( ~ v2_struct_0(sK0)
    | spl225_1 ),
    inference(avatar_component_clause,[],[f5571])).

fof(f5571,plain,
    ( spl225_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_1])])).

fof(f30068,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_6
    | ~ spl225_10
    | ~ spl225_18
    | spl225_85
    | spl225_109
    | ~ spl225_140
    | ~ spl225_160
    | ~ spl225_176 ),
    inference(unit_resulting_resolution,[],[f5573,f5578,f5583,f5598,f5618,f10049,f24714,f5656,f9929,f12395,f29954,f4389])).

fof(f4389,plain,(
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
      | ~ r1_tsep_1(X3,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3454])).

fof(f3454,plain,(
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
    inference(flattening,[],[f3453])).

fof(f3453,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f29954,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl225_176 ),
    inference(avatar_component_clause,[],[f29952])).

fof(f29952,plain,
    ( spl225_176
  <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_176])])).

fof(f12395,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl225_140 ),
    inference(avatar_component_clause,[],[f12393])).

fof(f12393,plain,
    ( spl225_140
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_140])])).

fof(f9929,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | spl225_85 ),
    inference(avatar_component_clause,[],[f9927])).

fof(f9927,plain,
    ( spl225_85
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_85])])).

fof(f5656,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl225_18 ),
    inference(avatar_component_clause,[],[f5654])).

fof(f5654,plain,
    ( spl225_18
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_18])])).

fof(f24714,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | ~ spl225_160 ),
    inference(avatar_component_clause,[],[f24712])).

fof(f24712,plain,
    ( spl225_160
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_160])])).

fof(f10049,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | spl225_109 ),
    inference(avatar_component_clause,[],[f10047])).

fof(f10047,plain,
    ( spl225_109
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_109])])).

fof(f29955,plain,
    ( spl225_176
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_4
    | spl225_6
    | ~ spl225_8
    | ~ spl225_10 ),
    inference(avatar_split_clause,[],[f6091,f5616,f5606,f5596,f5586,f5581,f5576,f5571,f29952])).

fof(f5586,plain,
    ( spl225_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_4])])).

fof(f5606,plain,
    ( spl225_8
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_8])])).

fof(f6091,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_4
    | spl225_6
    | ~ spl225_8
    | ~ spl225_10 ),
    inference(backward_demodulation,[],[f5997,f6056])).

fof(f6056,plain,
    ( k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1)
    | spl225_1
    | ~ spl225_3
    | spl225_4
    | spl225_6
    | ~ spl225_8
    | ~ spl225_10 ),
    inference(unit_resulting_resolution,[],[f5573,f5583,f5588,f5608,f5598,f5618,f4311])).

fof(f4311,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3402])).

fof(f3402,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3401])).

fof(f3401,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f5608,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl225_8 ),
    inference(avatar_component_clause,[],[f5606])).

fof(f5588,plain,
    ( ~ v2_struct_0(sK1)
    | spl225_4 ),
    inference(avatar_component_clause,[],[f5586])).

fof(f5997,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK1))
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_4
    | spl225_6
    | ~ spl225_8
    | ~ spl225_10 ),
    inference(unit_resulting_resolution,[],[f5573,f5578,f5583,f5598,f5618,f5588,f5608,f4334])).

fof(f4334,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3420])).

fof(f3420,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3419])).

fof(f3419,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3357])).

fof(f3357,axiom,(
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
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f25913,plain,
    ( spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_4
    | spl225_5
    | spl225_7
    | ~ spl225_8
    | ~ spl225_9
    | ~ spl225_11
    | ~ spl225_12
    | spl225_15
    | ~ spl225_18
    | spl225_85
    | spl225_109
    | ~ spl225_140
    | ~ spl225_160
    | ~ spl225_164 ),
    inference(avatar_contradiction_clause,[],[f25912])).

fof(f25912,plain,
    ( $false
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_4
    | spl225_5
    | spl225_7
    | ~ spl225_8
    | ~ spl225_9
    | ~ spl225_11
    | ~ spl225_12
    | spl225_15
    | ~ spl225_18
    | spl225_85
    | spl225_109
    | ~ spl225_140
    | ~ spl225_160
    | ~ spl225_164 ),
    inference(subsumption_resolution,[],[f25908,f17680])).

fof(f17680,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_4
    | spl225_5
    | spl225_7
    | ~ spl225_8
    | ~ spl225_9
    | ~ spl225_11
    | ~ spl225_12
    | spl225_15 ),
    inference(unit_resulting_resolution,[],[f5573,f5593,f5583,f5603,f5628,f5613,f5588,f5578,f5623,f5608,f5642,f4350])).

fof(f4350,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3434])).

fof(f5642,plain,
    ( ~ r1_tsep_1(sK4,sK1)
    | spl225_15 ),
    inference(avatar_component_clause,[],[f5640])).

fof(f5640,plain,
    ( spl225_15
  <=> r1_tsep_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_15])])).

fof(f5628,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl225_12 ),
    inference(avatar_component_clause,[],[f5626])).

fof(f5626,plain,
    ( spl225_12
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_12])])).

fof(f25908,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_4
    | ~ spl225_8
    | ~ spl225_18
    | spl225_85
    | spl225_109
    | ~ spl225_140
    | ~ spl225_160
    | ~ spl225_164 ),
    inference(unit_resulting_resolution,[],[f5573,f5578,f5583,f5588,f5608,f10049,f24714,f5656,f9929,f12395,f25818,f4389])).

fof(f25818,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl225_164 ),
    inference(avatar_component_clause,[],[f25816])).

fof(f25816,plain,
    ( spl225_164
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_164])])).

fof(f25819,plain,
    ( spl225_164
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_4
    | spl225_6
    | ~ spl225_8
    | ~ spl225_10 ),
    inference(avatar_split_clause,[],[f6005,f5616,f5606,f5596,f5586,f5581,f5576,f5571,f25816])).

fof(f6005,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK3))
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_4
    | spl225_6
    | ~ spl225_8
    | ~ spl225_10 ),
    inference(unit_resulting_resolution,[],[f5573,f5578,f5583,f5588,f5608,f5598,f5618,f4334])).

fof(f24715,plain,
    ( spl225_160
    | spl225_1
    | ~ spl225_3
    | spl225_5
    | spl225_7
    | ~ spl225_9
    | ~ spl225_11 ),
    inference(avatar_split_clause,[],[f5859,f5621,f5611,f5601,f5591,f5581,f5571,f24712])).

fof(f5859,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | spl225_1
    | ~ spl225_3
    | spl225_5
    | spl225_7
    | ~ spl225_9
    | ~ spl225_11 ),
    inference(unit_resulting_resolution,[],[f5573,f5583,f5593,f5613,f5603,f5623,f4340])).

fof(f4340,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3426])).

fof(f3426,plain,(
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
    inference(flattening,[],[f3425])).

fof(f3425,plain,(
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
    inference(ennf_transformation,[],[f3331])).

fof(f3331,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f12396,plain,
    ( spl225_140
    | spl225_1
    | ~ spl225_3
    | spl225_4
    | spl225_6
    | ~ spl225_8
    | ~ spl225_10 ),
    inference(avatar_split_clause,[],[f5828,f5616,f5606,f5596,f5586,f5581,f5571,f12393])).

fof(f5828,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | spl225_1
    | ~ spl225_3
    | spl225_4
    | spl225_6
    | ~ spl225_8
    | ~ spl225_10 ),
    inference(unit_resulting_resolution,[],[f5573,f5583,f5588,f5608,f5598,f5618,f4310])).

fof(f4310,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3400])).

fof(f3400,plain,(
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
    inference(flattening,[],[f3399])).

fof(f3399,plain,(
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
    inference(ennf_transformation,[],[f3330])).

fof(f3330,axiom,(
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

fof(f10904,plain,
    ( spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_5
    | spl225_6
    | spl225_7
    | ~ spl225_9
    | ~ spl225_10
    | ~ spl225_11
    | ~ spl225_13
    | spl225_14
    | ~ spl225_17 ),
    inference(avatar_contradiction_clause,[],[f10903])).

fof(f10903,plain,
    ( $false
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_5
    | spl225_6
    | spl225_7
    | ~ spl225_9
    | ~ spl225_10
    | ~ spl225_11
    | ~ spl225_13
    | spl225_14
    | ~ spl225_17 ),
    inference(subsumption_resolution,[],[f5652,f6305])).

fof(f6305,plain,
    ( ~ r1_tsep_1(sK2,sK4)
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_5
    | spl225_6
    | spl225_7
    | ~ spl225_9
    | ~ spl225_10
    | ~ spl225_11
    | ~ spl225_13
    | spl225_14 ),
    inference(unit_resulting_resolution,[],[f5573,f5603,f5583,f5598,f5633,f5623,f5593,f5618,f5638,f5613,f5578,f4389])).

fof(f5652,plain,
    ( r1_tsep_1(sK2,sK4)
    | ~ spl225_17 ),
    inference(avatar_component_clause,[],[f5650])).

fof(f5650,plain,
    ( spl225_17
  <=> r1_tsep_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl225_17])])).

fof(f10050,plain,
    ( ~ spl225_109
    | spl225_1
    | ~ spl225_3
    | spl225_5
    | spl225_7
    | ~ spl225_9
    | ~ spl225_11 ),
    inference(avatar_split_clause,[],[f5780,f5621,f5611,f5601,f5591,f5581,f5571,f10047])).

fof(f5780,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | spl225_1
    | ~ spl225_3
    | spl225_5
    | spl225_7
    | ~ spl225_9
    | ~ spl225_11 ),
    inference(unit_resulting_resolution,[],[f5573,f5583,f5593,f5613,f5603,f5623,f4338])).

fof(f4338,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3426])).

fof(f9930,plain,
    ( ~ spl225_85
    | spl225_1
    | ~ spl225_3
    | spl225_4
    | spl225_6
    | ~ spl225_8
    | ~ spl225_10 ),
    inference(avatar_split_clause,[],[f5724,f5616,f5606,f5596,f5586,f5581,f5571,f9927])).

fof(f5724,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | spl225_1
    | ~ spl225_3
    | spl225_4
    | spl225_6
    | ~ spl225_8
    | ~ spl225_10 ),
    inference(unit_resulting_resolution,[],[f5573,f5583,f5588,f5608,f5598,f5618,f4308])).

fof(f4308,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3400])).

fof(f6301,plain,
    ( spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_4
    | spl225_5
    | spl225_7
    | ~ spl225_8
    | ~ spl225_9
    | ~ spl225_11
    | ~ spl225_12
    | spl225_15
    | ~ spl225_17 ),
    inference(avatar_contradiction_clause,[],[f6300])).

fof(f6300,plain,
    ( $false
    | spl225_1
    | ~ spl225_2
    | ~ spl225_3
    | spl225_4
    | spl225_5
    | spl225_7
    | ~ spl225_8
    | ~ spl225_9
    | ~ spl225_11
    | ~ spl225_12
    | spl225_15
    | ~ spl225_17 ),
    inference(subsumption_resolution,[],[f6261,f5578])).

fof(f6261,plain,
    ( ~ v2_pre_topc(sK0)
    | spl225_1
    | ~ spl225_3
    | spl225_4
    | spl225_5
    | spl225_7
    | ~ spl225_8
    | ~ spl225_9
    | ~ spl225_11
    | ~ spl225_12
    | spl225_15
    | ~ spl225_17 ),
    inference(unit_resulting_resolution,[],[f5573,f5593,f5583,f5588,f5623,f5608,f5613,f5603,f5652,f5628,f5642,f4387])).

fof(f4387,plain,(
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
    inference(cnf_transformation,[],[f3454])).

fof(f5657,plain,
    ( spl225_17
    | spl225_18 ),
    inference(avatar_split_clause,[],[f4303,f5654,f5650])).

fof(f4303,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f3964])).

fof(f3964,plain,
    ( ( ~ r1_tsep_1(sK4,sK1)
      | ~ r1_tsep_1(sK2,sK3) )
    & ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
      | r1_tsep_1(sK2,sK4) )
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f3396,f3963,f3962,f3961,f3960,f3959])).

fof(f3959,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_tsep_1(X4,X1)
                          | ~ r1_tsep_1(X2,X3) )
                        & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                          | r1_tsep_1(X2,X4) )
                        & m1_pre_topc(X3,X4)
                        & m1_pre_topc(X1,X2)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
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

fof(f3960,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r1_tsep_1(X4,X1)
                      | ~ r1_tsep_1(X2,X3) )
                    & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3))
                      | r1_tsep_1(X2,X4) )
                    & m1_pre_topc(X3,X4)
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r1_tsep_1(X4,sK1)
                    | ~ r1_tsep_1(X2,X3) )
                  & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,sK1,X3))
                    | r1_tsep_1(X2,X4) )
                  & m1_pre_topc(X3,X4)
                  & m1_pre_topc(sK1,X2)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3961,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r1_tsep_1(X4,sK1)
                  | ~ r1_tsep_1(X2,X3) )
                & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,sK1,X3))
                  | r1_tsep_1(X2,X4) )
                & m1_pre_topc(X3,X4)
                & m1_pre_topc(sK1,X2)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r1_tsep_1(X4,sK1)
                | ~ r1_tsep_1(sK2,X3) )
              & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,X3))
                | r1_tsep_1(sK2,X4) )
              & m1_pre_topc(X3,X4)
              & m1_pre_topc(sK1,sK2)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3962,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ r1_tsep_1(X4,sK1)
              | ~ r1_tsep_1(sK2,X3) )
            & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,X3))
              | r1_tsep_1(sK2,X4) )
            & m1_pre_topc(X3,X4)
            & m1_pre_topc(sK1,sK2)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ r1_tsep_1(X4,sK1)
            | ~ r1_tsep_1(sK2,sK3) )
          & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,sK3))
            | r1_tsep_1(sK2,X4) )
          & m1_pre_topc(sK3,X4)
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3963,plain,
    ( ? [X4] :
        ( ( ~ r1_tsep_1(X4,sK1)
          | ~ r1_tsep_1(sK2,sK3) )
        & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,sK3))
          | r1_tsep_1(sK2,X4) )
        & m1_pre_topc(sK3,X4)
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ( ~ r1_tsep_1(sK4,sK1)
        | ~ r1_tsep_1(sK2,sK3) )
      & ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(sK2,sK4) )
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3396,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3395])).

fof(f3395,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3376])).

fof(f3376,negated_conjecture,(
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
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X3,X4)
                            & m1_pre_topc(X1,X2) )
                         => ( ( r1_tsep_1(X4,X1)
                              & r1_tsep_1(X2,X3) )
                            | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                              & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3375])).

fof(f3375,conjecture,(
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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => ( ( r1_tsep_1(X4,X1)
                            & r1_tsep_1(X2,X3) )
                          | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                            & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tmap_1)).

fof(f5643,plain,
    ( ~ spl225_14
    | ~ spl225_15 ),
    inference(avatar_split_clause,[],[f4304,f5640,f5636])).

fof(f4304,plain,
    ( ~ r1_tsep_1(sK4,sK1)
    | ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5634,plain,(
    spl225_13 ),
    inference(avatar_split_clause,[],[f4302,f5631])).

fof(f4302,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5629,plain,(
    spl225_12 ),
    inference(avatar_split_clause,[],[f4301,f5626])).

fof(f4301,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5624,plain,(
    spl225_11 ),
    inference(avatar_split_clause,[],[f4300,f5621])).

fof(f4300,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5619,plain,(
    spl225_10 ),
    inference(avatar_split_clause,[],[f4298,f5616])).

fof(f4298,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5614,plain,(
    spl225_9 ),
    inference(avatar_split_clause,[],[f4296,f5611])).

fof(f4296,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5609,plain,(
    spl225_8 ),
    inference(avatar_split_clause,[],[f4294,f5606])).

fof(f4294,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5604,plain,(
    ~ spl225_7 ),
    inference(avatar_split_clause,[],[f4299,f5601])).

fof(f4299,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5599,plain,(
    ~ spl225_6 ),
    inference(avatar_split_clause,[],[f4297,f5596])).

fof(f4297,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5594,plain,(
    ~ spl225_5 ),
    inference(avatar_split_clause,[],[f4295,f5591])).

fof(f4295,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5589,plain,(
    ~ spl225_4 ),
    inference(avatar_split_clause,[],[f4293,f5586])).

fof(f4293,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5584,plain,(
    spl225_3 ),
    inference(avatar_split_clause,[],[f4292,f5581])).

fof(f4292,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5579,plain,(
    spl225_2 ),
    inference(avatar_split_clause,[],[f4291,f5576])).

fof(f4291,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3964])).

fof(f5574,plain,(
    ~ spl225_1 ),
    inference(avatar_split_clause,[],[f4290,f5571])).

fof(f4290,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3964])).
%------------------------------------------------------------------------------
