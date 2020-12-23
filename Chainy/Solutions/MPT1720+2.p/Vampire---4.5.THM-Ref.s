%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1720+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:30 EST 2020

% Result     : Theorem 2.85s
% Output     : Refutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 296 expanded)
%              Number of leaves         :   29 ( 156 expanded)
%              Depth                    :    7
%              Number of atoms          :  466 (2034 expanded)
%              Number of equality atoms :   19 (  31 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6940,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3855,f3860,f3865,f3870,f3875,f3880,f3885,f3890,f3895,f3900,f3905,f3910,f4015,f4896,f5894,f6002,f6537,f6641,f6716,f6923])).

fof(f6923,plain,
    ( spl52_443
    | ~ spl52_2
    | ~ spl52_3
    | ~ spl52_4
    | spl52_5
    | ~ spl52_6
    | spl52_7
    | ~ spl52_8
    | spl52_9
    | ~ spl52_10
    | ~ spl52_11
    | spl52_12
    | ~ spl52_426 ),
    inference(avatar_split_clause,[],[f6922,f6574,f3907,f3902,f3897,f3892,f3887,f3882,f3877,f3872,f3867,f3862,f3857,f6713])).

fof(f6713,plain,
    ( spl52_443
  <=> m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_443])])).

fof(f3857,plain,
    ( spl52_2
  <=> m1_pre_topc(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_2])])).

fof(f3862,plain,
    ( spl52_3
  <=> m1_pre_topc(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_3])])).

fof(f3867,plain,
    ( spl52_4
  <=> m1_pre_topc(sK7,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_4])])).

fof(f3872,plain,
    ( spl52_5
  <=> v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_5])])).

fof(f3877,plain,
    ( spl52_6
  <=> m1_pre_topc(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_6])])).

fof(f3882,plain,
    ( spl52_7
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_7])])).

fof(f3887,plain,
    ( spl52_8
  <=> m1_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_8])])).

fof(f3892,plain,
    ( spl52_9
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_9])])).

fof(f3897,plain,
    ( spl52_10
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_10])])).

fof(f3902,plain,
    ( spl52_11
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_11])])).

fof(f3907,plain,
    ( spl52_12
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_12])])).

fof(f6574,plain,
    ( spl52_426
  <=> k1_tsep_1(sK4,sK5,sK6) = k1_tsep_1(sK4,sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_426])])).

fof(f6922,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),k1_tsep_1(sK4,sK5,sK6))
    | ~ spl52_2
    | ~ spl52_3
    | ~ spl52_4
    | spl52_5
    | ~ spl52_6
    | spl52_7
    | ~ spl52_8
    | spl52_9
    | ~ spl52_10
    | ~ spl52_11
    | spl52_12
    | ~ spl52_426 ),
    inference(forward_demodulation,[],[f6804,f6576])).

fof(f6576,plain,
    ( k1_tsep_1(sK4,sK5,sK6) = k1_tsep_1(sK4,sK6,sK6)
    | ~ spl52_426 ),
    inference(avatar_component_clause,[],[f6574])).

fof(f6804,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),k1_tsep_1(sK4,sK6,sK6))
    | ~ spl52_2
    | ~ spl52_3
    | ~ spl52_4
    | spl52_5
    | ~ spl52_6
    | spl52_7
    | ~ spl52_8
    | spl52_9
    | ~ spl52_10
    | ~ spl52_11
    | spl52_12 ),
    inference(unit_resulting_resolution,[],[f3909,f3904,f3899,f3894,f3884,f3889,f3864,f3879,f3874,f3884,f3869,f3879,f3859,f3631])).

fof(f3631,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3387])).

fof(f3387,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      | ~ m1_pre_topc(X3,X4)
                      | ~ m1_pre_topc(X1,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3386])).

fof(f3386,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      | ~ m1_pre_topc(X3,X4)
                      | ~ m1_pre_topc(X1,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3363])).

fof(f3363,axiom,(
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
                       => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tmap_1)).

fof(f3859,plain,
    ( m1_pre_topc(sK7,sK6)
    | ~ spl52_2 ),
    inference(avatar_component_clause,[],[f3857])).

fof(f3869,plain,
    ( m1_pre_topc(sK7,sK4)
    | ~ spl52_4 ),
    inference(avatar_component_clause,[],[f3867])).

fof(f3874,plain,
    ( ~ v2_struct_0(sK7)
    | spl52_5 ),
    inference(avatar_component_clause,[],[f3872])).

fof(f3879,plain,
    ( m1_pre_topc(sK6,sK4)
    | ~ spl52_6 ),
    inference(avatar_component_clause,[],[f3877])).

fof(f3864,plain,
    ( m1_pre_topc(sK5,sK6)
    | ~ spl52_3 ),
    inference(avatar_component_clause,[],[f3862])).

fof(f3889,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl52_8 ),
    inference(avatar_component_clause,[],[f3887])).

fof(f3884,plain,
    ( ~ v2_struct_0(sK6)
    | spl52_7 ),
    inference(avatar_component_clause,[],[f3882])).

fof(f3894,plain,
    ( ~ v2_struct_0(sK5)
    | spl52_9 ),
    inference(avatar_component_clause,[],[f3892])).

fof(f3899,plain,
    ( l1_pre_topc(sK4)
    | ~ spl52_10 ),
    inference(avatar_component_clause,[],[f3897])).

fof(f3904,plain,
    ( v2_pre_topc(sK4)
    | ~ spl52_11 ),
    inference(avatar_component_clause,[],[f3902])).

fof(f3909,plain,
    ( ~ v2_struct_0(sK4)
    | spl52_12 ),
    inference(avatar_component_clause,[],[f3907])).

fof(f6716,plain,
    ( ~ spl52_443
    | spl52_346
    | ~ spl52_426 ),
    inference(avatar_split_clause,[],[f6705,f6574,f5999,f6713])).

fof(f5999,plain,
    ( spl52_346
  <=> m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),k1_tsep_1(sK4,sK6,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_346])])).

fof(f6705,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),k1_tsep_1(sK4,sK5,sK6))
    | spl52_346
    | ~ spl52_426 ),
    inference(backward_demodulation,[],[f6001,f6576])).

fof(f6001,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),k1_tsep_1(sK4,sK6,sK6))
    | spl52_346 ),
    inference(avatar_component_clause,[],[f5999])).

fof(f6641,plain,
    ( spl52_426
    | ~ spl52_327
    | ~ spl52_417 ),
    inference(avatar_split_clause,[],[f6640,f6534,f5891,f6574])).

fof(f5891,plain,
    ( spl52_327
  <=> g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = k1_tsep_1(sK4,sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_327])])).

fof(f6534,plain,
    ( spl52_417
  <=> g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = k1_tsep_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_417])])).

fof(f6640,plain,
    ( k1_tsep_1(sK4,sK5,sK6) = k1_tsep_1(sK4,sK6,sK6)
    | ~ spl52_327
    | ~ spl52_417 ),
    inference(backward_demodulation,[],[f5893,f6536])).

fof(f6536,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = k1_tsep_1(sK4,sK5,sK6)
    | ~ spl52_417 ),
    inference(avatar_component_clause,[],[f6534])).

fof(f5893,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = k1_tsep_1(sK4,sK6,sK6)
    | ~ spl52_327 ),
    inference(avatar_component_clause,[],[f5891])).

fof(f6537,plain,
    ( spl52_417
    | ~ spl52_3
    | ~ spl52_6
    | spl52_7
    | ~ spl52_8
    | spl52_9
    | ~ spl52_10
    | ~ spl52_11
    | spl52_12 ),
    inference(avatar_split_clause,[],[f6501,f3907,f3902,f3897,f3892,f3887,f3882,f3877,f3862,f6534])).

fof(f6501,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = k1_tsep_1(sK4,sK5,sK6)
    | ~ spl52_3
    | ~ spl52_6
    | spl52_7
    | ~ spl52_8
    | spl52_9
    | ~ spl52_10
    | ~ spl52_11
    | spl52_12 ),
    inference(unit_resulting_resolution,[],[f3909,f3904,f3899,f3894,f3884,f3889,f3879,f3864,f3650])).

fof(f3650,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3534])).

fof(f3534,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X2)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3399])).

fof(f3399,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3398])).

fof(f3398,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3359])).

fof(f3359,axiom,(
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
             => ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

fof(f6002,plain,
    ( ~ spl52_346
    | spl52_173
    | ~ spl52_327 ),
    inference(avatar_split_clause,[],[f5986,f5891,f4892,f5999])).

fof(f4892,plain,
    ( spl52_173
  <=> m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_173])])).

fof(f5986,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),k1_tsep_1(sK4,sK6,sK6))
    | spl52_173
    | ~ spl52_327 ),
    inference(backward_demodulation,[],[f4894,f5893])).

fof(f4894,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | spl52_173 ),
    inference(avatar_component_clause,[],[f4892])).

fof(f5894,plain,
    ( spl52_327
    | ~ spl52_6
    | spl52_7
    | ~ spl52_10
    | ~ spl52_11
    | spl52_12 ),
    inference(avatar_split_clause,[],[f5877,f3907,f3902,f3897,f3882,f3877,f5891])).

fof(f5877,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = k1_tsep_1(sK4,sK6,sK6)
    | ~ spl52_6
    | spl52_7
    | ~ spl52_10
    | ~ spl52_11
    | spl52_12 ),
    inference(unit_resulting_resolution,[],[f3909,f3904,f3899,f3884,f3879,f3653])).

fof(f3653,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3403])).

fof(f3403,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3402])).

fof(f3402,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3361])).

fof(f3361,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f4896,plain,
    ( ~ spl52_29
    | ~ spl52_173
    | spl52_1 ),
    inference(avatar_split_clause,[],[f4890,f3852,f4892,f4012])).

fof(f4012,plain,
    ( spl52_29
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_29])])).

fof(f3852,plain,
    ( spl52_1
  <=> m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_1])])).

fof(f4890,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ l1_pre_topc(sK6)
    | spl52_1 ),
    inference(resolution,[],[f3683,f3854])).

fof(f3854,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),sK6)
    | spl52_1 ),
    inference(avatar_component_clause,[],[f3852])).

fof(f3683,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3430])).

fof(f3430,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1850])).

fof(f1850,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f4015,plain,
    ( spl52_29
    | ~ spl52_6
    | ~ spl52_10 ),
    inference(avatar_split_clause,[],[f4004,f3897,f3877,f4012])).

fof(f4004,plain,
    ( l1_pre_topc(sK6)
    | ~ spl52_6
    | ~ spl52_10 ),
    inference(unit_resulting_resolution,[],[f3899,f3879,f3710])).

fof(f3710,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3453])).

fof(f3453,plain,(
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

fof(f3910,plain,(
    ~ spl52_12 ),
    inference(avatar_split_clause,[],[f3612,f3907])).

fof(f3612,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f3522])).

fof(f3522,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),sK6)
    & m1_pre_topc(sK7,sK6)
    & m1_pre_topc(sK5,sK6)
    & m1_pre_topc(sK7,sK4)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f3379,f3521,f3520,f3519,f3518])).

fof(f3518,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                    & m1_pre_topc(X3,X2)
                    & m1_pre_topc(X1,X2)
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
                  ( ~ m1_pre_topc(k1_tsep_1(sK4,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK4)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3519,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k1_tsep_1(sK4,X1,X3),X2)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK4)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK4)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,X3),X2)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(sK5,X2)
              & m1_pre_topc(X3,sK4)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK4)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK5,sK4)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f3520,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,X3),X2)
            & m1_pre_topc(X3,X2)
            & m1_pre_topc(sK5,X2)
            & m1_pre_topc(X3,sK4)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK4)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,X3),sK6)
          & m1_pre_topc(X3,sK6)
          & m1_pre_topc(sK5,sK6)
          & m1_pre_topc(X3,sK4)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK6,sK4)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f3521,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,X3),sK6)
        & m1_pre_topc(X3,sK6)
        & m1_pre_topc(sK5,sK6)
        & m1_pre_topc(X3,sK4)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),sK6)
      & m1_pre_topc(sK7,sK6)
      & m1_pre_topc(sK5,sK6)
      & m1_pre_topc(sK7,sK4)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f3379,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3378])).

fof(f3378,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3366])).

fof(f3366,negated_conjecture,(
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
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3365])).

fof(f3365,conjecture,(
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
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f3905,plain,(
    spl52_11 ),
    inference(avatar_split_clause,[],[f3613,f3902])).

fof(f3613,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3522])).

fof(f3900,plain,(
    spl52_10 ),
    inference(avatar_split_clause,[],[f3614,f3897])).

fof(f3614,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3522])).

fof(f3895,plain,(
    ~ spl52_9 ),
    inference(avatar_split_clause,[],[f3615,f3892])).

fof(f3615,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f3522])).

fof(f3890,plain,(
    spl52_8 ),
    inference(avatar_split_clause,[],[f3616,f3887])).

fof(f3616,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f3522])).

fof(f3885,plain,(
    ~ spl52_7 ),
    inference(avatar_split_clause,[],[f3617,f3882])).

fof(f3617,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f3522])).

fof(f3880,plain,(
    spl52_6 ),
    inference(avatar_split_clause,[],[f3618,f3877])).

fof(f3618,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f3522])).

fof(f3875,plain,(
    ~ spl52_5 ),
    inference(avatar_split_clause,[],[f3619,f3872])).

fof(f3619,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f3522])).

fof(f3870,plain,(
    spl52_4 ),
    inference(avatar_split_clause,[],[f3620,f3867])).

fof(f3620,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f3522])).

fof(f3865,plain,(
    spl52_3 ),
    inference(avatar_split_clause,[],[f3621,f3862])).

fof(f3621,plain,(
    m1_pre_topc(sK5,sK6) ),
    inference(cnf_transformation,[],[f3522])).

fof(f3860,plain,(
    spl52_2 ),
    inference(avatar_split_clause,[],[f3622,f3857])).

fof(f3622,plain,(
    m1_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f3522])).

fof(f3855,plain,(
    ~ spl52_1 ),
    inference(avatar_split_clause,[],[f3623,f3852])).

fof(f3623,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK4,sK5,sK7),sK6) ),
    inference(cnf_transformation,[],[f3522])).
%------------------------------------------------------------------------------
