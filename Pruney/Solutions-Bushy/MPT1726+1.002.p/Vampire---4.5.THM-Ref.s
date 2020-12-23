%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1726+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:26 EST 2020

% Result     : Theorem 3.00s
% Output     : Refutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  434 (2996 expanded)
%              Number of leaves         :  124 (1608 expanded)
%              Depth                    :    7
%              Number of atoms          : 2334 (11166 expanded)
%              Number of equality atoms :   10 (  30 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9936,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f83,f88,f93,f98,f103,f108,f113,f118,f127,f136,f157,f226,f308,f328,f339,f344,f349,f354,f359,f364,f369,f374,f379,f384,f389,f394,f399,f404,f409,f414,f419,f424,f429,f434,f439,f444,f449,f454,f459,f464,f469,f474,f479,f484,f489,f494,f499,f504,f509,f514,f519,f524,f529,f534,f539,f544,f549,f554,f559,f564,f569,f574,f579,f584,f589,f594,f599,f604,f609,f614,f619,f624,f629,f634,f639,f644,f649,f654,f659,f664,f669,f674,f679,f684,f689,f694,f699,f704,f709,f714,f719,f724,f729,f734,f739,f744,f749,f754,f759,f764,f769,f774,f779,f784,f789,f794,f799,f804,f9816,f9829,f9831,f9838,f9839,f9847,f9935])).

fof(f9935,plain,
    ( spl5_1
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15
    | ~ spl5_16
    | spl5_20
    | spl5_46
    | ~ spl5_73
    | ~ spl5_88
    | ~ spl5_111 ),
    inference(avatar_contradiction_clause,[],[f9934])).

fof(f9934,plain,
    ( $false
    | spl5_1
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15
    | ~ spl5_16
    | spl5_20
    | spl5_46
    | ~ spl5_73
    | ~ spl5_88
    | ~ spl5_111 ),
    inference(subsumption_resolution,[],[f9932,f9821])).

fof(f9821,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | spl5_1
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f77,f57,f82,f102,f92,f87,f62,f107,f112,f67,f126,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X3)
      | ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f126,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_15
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f67,plain,
    ( ~ v2_struct_0(sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f112,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_12
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f107,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_11
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f62,plain,
    ( ~ v2_struct_0(sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f87,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f92,plain,
    ( m1_pre_topc(sK4,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_8
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f102,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_10
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f82,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f57,plain,
    ( ~ v2_struct_0(sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_1
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f77,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f9932,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | spl5_2
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_16
    | spl5_20
    | spl5_46
    | ~ spl5_73
    | ~ spl5_88
    | ~ spl5_111 ),
    inference(unit_resulting_resolution,[],[f77,f62,f82,f87,f107,f463,f673,f131,f598,f307,f788,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ r1_tsep_1(X3,X2)
      | r1_tsep_1(X3,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f788,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl5_111 ),
    inference(avatar_component_clause,[],[f786])).

fof(f786,plain,
    ( spl5_111
  <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f307,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl5_20
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f598,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f596])).

fof(f596,plain,
    ( spl5_73
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f131,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_16
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f673,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl5_88
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f463,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | spl5_46 ),
    inference(avatar_component_clause,[],[f461])).

fof(f461,plain,
    ( spl5_46
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f9847,plain,
    ( ~ spl5_117
    | spl5_1
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | spl5_21 ),
    inference(avatar_split_clause,[],[f9819,f325,f120,f115,f110,f90,f85,f80,f75,f70,f65,f55,f9844])).

fof(f9844,plain,
    ( spl5_117
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f70,plain,
    ( spl5_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f115,plain,
    ( spl5_13
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f120,plain,
    ( spl5_14
  <=> r1_tsep_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f325,plain,
    ( spl5_21
  <=> r1_tsep_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f9819,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | spl5_1
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | spl5_21 ),
    inference(unit_resulting_resolution,[],[f87,f82,f77,f67,f57,f327,f112,f92,f117,f72,f121,f44])).

fof(f121,plain,
    ( r1_tsep_1(sK4,sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f72,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f117,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f327,plain,
    ( ~ r1_tsep_1(sK4,sK2)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f325])).

fof(f9839,plain,
    ( ~ spl5_17
    | spl5_1
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15 ),
    inference(avatar_split_clause,[],[f9823,f124,f110,f105,f100,f90,f85,f80,f75,f65,f60,f55,f133])).

fof(f133,plain,
    ( spl5_17
  <=> r1_tsep_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f9823,plain,
    ( ~ r1_tsep_1(sK2,sK4)
    | spl5_1
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f82,f67,f57,f77,f102,f92,f87,f112,f107,f62,f126,f44])).

fof(f9838,plain,
    ( spl5_116
    | spl5_1
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f9818,f120,f115,f105,f100,f90,f85,f80,f75,f70,f60,f55,f9835])).

fof(f9835,plain,
    ( spl5_116
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f9818,plain,
    ( r1_tsep_1(sK3,sK1)
    | spl5_1
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f87,f82,f77,f62,f72,f102,f107,f117,f92,f57,f121,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ r1_tsep_1(X2,X3)
      | r1_tsep_1(X1,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9831,plain,
    ( spl5_1
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f9830])).

fof(f9830,plain,
    ( $false
    | spl5_1
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f135,f9823])).

fof(f135,plain,
    ( r1_tsep_1(sK2,sK4)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f9829,plain,
    ( spl5_115
    | spl5_1
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f9817,f120,f115,f105,f100,f90,f85,f80,f75,f70,f60,f55,f9826])).

fof(f9826,plain,
    ( spl5_115
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f9817,plain,
    ( r1_tsep_1(sK1,sK3)
    | spl5_1
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f87,f82,f77,f62,f72,f102,f107,f117,f92,f57,f121,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ r1_tsep_1(X2,X3)
      | r1_tsep_1(X3,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9816,plain,
    ( spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_13
    | ~ spl5_16
    | spl5_20
    | spl5_46
    | ~ spl5_73
    | ~ spl5_88
    | ~ spl5_99
    | spl5_114 ),
    inference(avatar_contradiction_clause,[],[f9815])).

fof(f9815,plain,
    ( $false
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_13
    | ~ spl5_16
    | spl5_20
    | spl5_46
    | ~ spl5_73
    | ~ spl5_88
    | ~ spl5_99
    | spl5_114 ),
    inference(subsumption_resolution,[],[f9813,f803])).

fof(f803,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | spl5_114 ),
    inference(avatar_component_clause,[],[f801])).

fof(f801,plain,
    ( spl5_114
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f9813,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_13
    | ~ spl5_16
    | spl5_20
    | spl5_46
    | ~ spl5_73
    | ~ spl5_88
    | ~ spl5_99 ),
    inference(unit_resulting_resolution,[],[f77,f72,f82,f87,f117,f463,f673,f131,f598,f307,f728,f44])).

fof(f728,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl5_99 ),
    inference(avatar_component_clause,[],[f726])).

fof(f726,plain,
    ( spl5_99
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f804,plain,
    ( ~ spl5_114
    | spl5_1
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f329,f120,f115,f110,f95,f90,f85,f80,f75,f70,f65,f55,f801])).

fof(f95,plain,
    ( spl5_9
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f329,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | spl5_1
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(unit_resulting_resolution,[],[f82,f67,f72,f97,f112,f122,f117,f57,f92,f87,f77,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X3)
      | ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f122,plain,
    ( ~ r1_tsep_1(sK4,sK1)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f97,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f799,plain,
    ( ~ spl5_113
    | spl5_1
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f320,f120,f115,f110,f95,f90,f85,f80,f75,f70,f65,f55,f796])).

fof(f796,plain,
    ( spl5_113
  <=> r1_tsep_1(k2_tsep_1(sK0,sK4,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f320,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK4,sK2),sK1)
    | spl5_1
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(unit_resulting_resolution,[],[f82,f67,f72,f97,f112,f122,f117,f57,f92,f87,f77,f39])).

fof(f794,plain,
    ( spl5_112
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f296,f115,f110,f85,f80,f75,f70,f65,f791])).

fof(f791,plain,
    ( spl5_112
  <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f296,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f247,f263])).

fof(f263,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f87,f72,f117,f67,f112,f77,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f247,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK1))
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f67,f112,f87,f82,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f789,plain,
    ( spl5_111
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f292,f115,f105,f85,f80,f75,f70,f60,f786])).

fof(f292,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f251,f267])).

fof(f267,plain,
    ( k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1)
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f87,f72,f117,f62,f107,f77,f47])).

fof(f251,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK1))
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f62,f107,f87,f82,f38])).

fof(f784,plain,
    ( spl5_110
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f288,f110,f105,f85,f80,f75,f65,f60,f781])).

fof(f781,plain,
    ( spl5_110
  <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f288,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3))
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f252,f268])).

fof(f268,plain,
    ( k1_tsep_1(sK0,sK2,sK3) = k1_tsep_1(sK0,sK3,sK2)
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f87,f67,f112,f62,f107,f77,f47])).

fof(f252,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK2))
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f62,f107,f87,f82,f38])).

fof(f779,plain,
    ( spl5_109
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f284,f115,f90,f85,f80,f75,f70,f55,f776])).

fof(f776,plain,
    ( spl5_109
  <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f284,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4))
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f255,f271])).

fof(f271,plain,
    ( k1_tsep_1(sK0,sK1,sK4) = k1_tsep_1(sK0,sK4,sK1)
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f87,f72,f117,f57,f92,f77,f47])).

fof(f255,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK1))
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f57,f92,f87,f82,f38])).

fof(f774,plain,
    ( spl5_108
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f280,f110,f90,f85,f80,f75,f65,f55,f771])).

fof(f771,plain,
    ( spl5_108
  <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f280,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4))
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f256,f272])).

fof(f272,plain,
    ( k1_tsep_1(sK0,sK2,sK4) = k1_tsep_1(sK0,sK4,sK2)
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f87,f67,f112,f57,f92,f77,f47])).

fof(f256,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK2))
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f57,f92,f87,f82,f38])).

fof(f769,plain,
    ( spl5_107
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f276,f105,f90,f85,f80,f75,f60,f55,f766])).

fof(f766,plain,
    ( spl5_107
  <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f276,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4))
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f257,f273])).

fof(f273,plain,
    ( k1_tsep_1(sK0,sK3,sK4) = k1_tsep_1(sK0,sK4,sK3)
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f87,f62,f107,f57,f92,f77,f47])).

fof(f257,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK3))
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f57,f92,f87,f82,f38])).

fof(f764,plain,
    ( spl5_106
    | spl5_1
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f258,f90,f85,f80,f75,f55,f761])).

fof(f761,plain,
    ( spl5_106
  <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f258,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK4))
    | spl5_1
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f57,f92,f87,f82,f38])).

fof(f759,plain,
    ( spl5_105
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f254,f105,f90,f85,f80,f75,f60,f55,f756])).

fof(f756,plain,
    ( spl5_105
  <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f254,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK4))
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f62,f107,f87,f82,f38])).

fof(f754,plain,
    ( spl5_104
    | spl5_2
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f253,f105,f85,f80,f75,f60,f751])).

fof(f751,plain,
    ( spl5_104
  <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f253,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK3))
    | spl5_2
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f62,f107,f87,f82,f38])).

fof(f749,plain,
    ( spl5_103
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f250,f110,f90,f85,f80,f75,f65,f55,f746])).

fof(f746,plain,
    ( spl5_103
  <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f250,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK4))
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f67,f112,f87,f82,f38])).

fof(f744,plain,
    ( spl5_102
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f249,f110,f105,f85,f80,f75,f65,f60,f741])).

fof(f741,plain,
    ( spl5_102
  <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f249,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK3))
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f67,f112,f87,f82,f38])).

fof(f739,plain,
    ( spl5_101
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f248,f110,f85,f80,f75,f65,f736])).

fof(f736,plain,
    ( spl5_101
  <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f248,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2))
    | spl5_3
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f67,f112,f87,f82,f38])).

fof(f734,plain,
    ( spl5_100
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f246,f115,f90,f85,f80,f75,f70,f55,f731])).

fof(f731,plain,
    ( spl5_100
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f246,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK4))
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f72,f117,f87,f82,f38])).

fof(f729,plain,
    ( spl5_99
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f245,f115,f105,f85,f80,f75,f70,f60,f726])).

fof(f245,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK3))
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f72,f117,f87,f82,f38])).

fof(f724,plain,
    ( spl5_98
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f244,f115,f110,f85,f80,f75,f70,f65,f721])).

fof(f721,plain,
    ( spl5_98
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f244,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f72,f117,f87,f82,f38])).

fof(f719,plain,
    ( spl5_97
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f243,f115,f85,f80,f75,f70,f716])).

fof(f716,plain,
    ( spl5_97
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f243,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK1))
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f72,f117,f87,f82,f38])).

fof(f714,plain,
    ( spl5_96
    | spl5_1
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f242,f90,f85,f75,f55,f711])).

fof(f711,plain,
    ( spl5_96
  <=> m1_pre_topc(k2_tsep_1(sK0,sK4,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f242,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK4,sK4),sK0)
    | spl5_1
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f57,f92,f87,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f709,plain,
    ( spl5_95
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f241,f105,f90,f85,f75,f60,f55,f706])).

fof(f706,plain,
    ( spl5_95
  <=> m1_pre_topc(k2_tsep_1(sK0,sK4,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f241,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK4,sK3),sK0)
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f57,f92,f87,f53])).

fof(f704,plain,
    ( spl5_94
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f240,f110,f90,f85,f75,f65,f55,f701])).

fof(f701,plain,
    ( spl5_94
  <=> m1_pre_topc(k2_tsep_1(sK0,sK4,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f240,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK4,sK2),sK0)
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f57,f92,f87,f53])).

fof(f699,plain,
    ( spl5_93
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f239,f115,f90,f85,f75,f70,f55,f696])).

fof(f696,plain,
    ( spl5_93
  <=> m1_pre_topc(k2_tsep_1(sK0,sK4,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f239,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK4,sK1),sK0)
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f57,f92,f87,f53])).

fof(f694,plain,
    ( spl5_92
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f238,f105,f90,f85,f75,f60,f55,f691])).

fof(f691,plain,
    ( spl5_92
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f238,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f62,f107,f87,f53])).

fof(f689,plain,
    ( spl5_91
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f237,f105,f85,f75,f60,f686])).

fof(f686,plain,
    ( spl5_91
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f237,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK3),sK0)
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f62,f107,f87,f53])).

fof(f684,plain,
    ( spl5_90
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f236,f110,f105,f85,f75,f65,f60,f681])).

fof(f681,plain,
    ( spl5_90
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f236,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f62,f107,f87,f53])).

fof(f679,plain,
    ( spl5_89
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f235,f115,f105,f85,f75,f70,f60,f676])).

fof(f676,plain,
    ( spl5_89
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f235,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f62,f107,f87,f53])).

fof(f674,plain,
    ( spl5_88
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f234,f110,f90,f85,f75,f65,f55,f671])).

fof(f234,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f67,f112,f87,f53])).

fof(f669,plain,
    ( spl5_87
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f233,f110,f105,f85,f75,f65,f60,f666])).

fof(f666,plain,
    ( spl5_87
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f233,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f67,f112,f87,f53])).

fof(f664,plain,
    ( spl5_86
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f232,f110,f85,f75,f65,f661])).

fof(f661,plain,
    ( spl5_86
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f232,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK2),sK0)
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f67,f112,f87,f53])).

fof(f659,plain,
    ( spl5_85
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f231,f115,f110,f85,f75,f70,f65,f656])).

fof(f656,plain,
    ( spl5_85
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f231,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f67,f112,f87,f53])).

fof(f654,plain,
    ( spl5_84
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f230,f115,f90,f85,f75,f70,f55,f651])).

fof(f651,plain,
    ( spl5_84
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f230,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK4),sK0)
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f72,f117,f87,f53])).

fof(f649,plain,
    ( spl5_83
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f229,f115,f105,f85,f75,f70,f60,f646])).

fof(f646,plain,
    ( spl5_83
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f229,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f72,f117,f87,f53])).

fof(f644,plain,
    ( spl5_82
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f228,f115,f110,f85,f75,f70,f65,f641])).

fof(f641,plain,
    ( spl5_82
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f228,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f72,f117,f87,f53])).

fof(f639,plain,
    ( spl5_81
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f227,f115,f85,f75,f70,f636])).

fof(f636,plain,
    ( spl5_81
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f227,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK1),sK0)
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f72,f117,f87,f53])).

fof(f634,plain,
    ( spl5_80
    | spl5_1
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f221,f90,f85,f75,f55,f631])).

fof(f631,plain,
    ( spl5_80
  <=> m1_pre_topc(k1_tsep_1(sK0,sK4,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f221,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK4,sK4),sK0)
    | spl5_1
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f57,f92,f87,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f629,plain,
    ( spl5_79
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f217,f105,f90,f85,f75,f60,f55,f626])).

fof(f626,plain,
    ( spl5_79
  <=> m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f217,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0)
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f62,f107,f87,f50])).

fof(f624,plain,
    ( spl5_78
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f216,f105,f85,f75,f60,f621])).

fof(f621,plain,
    ( spl5_78
  <=> m1_pre_topc(k1_tsep_1(sK0,sK3,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f216,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK3,sK3),sK0)
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f62,f107,f87,f50])).

fof(f619,plain,
    ( spl5_77
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f213,f110,f90,f85,f75,f65,f55,f616])).

fof(f616,plain,
    ( spl5_77
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f213,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0)
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f67,f112,f87,f50])).

fof(f614,plain,
    ( spl5_76
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f212,f110,f105,f85,f75,f65,f60,f611])).

fof(f611,plain,
    ( spl5_76
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f212,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f67,f112,f87,f50])).

fof(f609,plain,
    ( spl5_75
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f211,f110,f85,f75,f65,f606])).

fof(f606,plain,
    ( spl5_75
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f211,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f67,f112,f87,f50])).

fof(f604,plain,
    ( spl5_74
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f209,f115,f90,f85,f75,f70,f55,f601])).

fof(f601,plain,
    ( spl5_74
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f209,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK4),sK0)
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f72,f117,f87,f50])).

fof(f599,plain,
    ( spl5_73
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f208,f115,f105,f85,f75,f70,f60,f596])).

fof(f208,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f72,f117,f87,f50])).

fof(f594,plain,
    ( spl5_72
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f207,f115,f110,f85,f75,f70,f65,f591])).

fof(f591,plain,
    ( spl5_72
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f207,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f72,f117,f87,f50])).

fof(f589,plain,
    ( spl5_71
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f206,f115,f85,f75,f70,f586])).

fof(f586,plain,
    ( spl5_71
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f206,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),sK0)
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f72,f117,f87,f50])).

fof(f584,plain,
    ( spl5_70
    | spl5_1
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f205,f90,f85,f75,f55,f581])).

fof(f581,plain,
    ( spl5_70
  <=> v1_pre_topc(k2_tsep_1(sK0,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f205,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK4,sK4))
    | spl5_1
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f57,f92,f87,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f579,plain,
    ( spl5_69
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f204,f105,f90,f85,f75,f60,f55,f576])).

fof(f576,plain,
    ( spl5_69
  <=> v1_pre_topc(k2_tsep_1(sK0,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f204,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK4,sK3))
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f57,f92,f87,f52])).

fof(f574,plain,
    ( spl5_68
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f203,f110,f90,f85,f75,f65,f55,f571])).

fof(f571,plain,
    ( spl5_68
  <=> v1_pre_topc(k2_tsep_1(sK0,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f203,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK4,sK2))
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f57,f92,f87,f52])).

fof(f569,plain,
    ( spl5_67
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f202,f115,f90,f85,f75,f70,f55,f566])).

fof(f566,plain,
    ( spl5_67
  <=> v1_pre_topc(k2_tsep_1(sK0,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f202,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK4,sK1))
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f57,f92,f87,f52])).

fof(f564,plain,
    ( spl5_66
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f201,f105,f90,f85,f75,f60,f55,f561])).

fof(f561,plain,
    ( spl5_66
  <=> v1_pre_topc(k2_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f201,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK3,sK4))
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f62,f107,f87,f52])).

fof(f559,plain,
    ( spl5_65
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f200,f105,f85,f75,f60,f556])).

fof(f556,plain,
    ( spl5_65
  <=> v1_pre_topc(k2_tsep_1(sK0,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f200,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK3,sK3))
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f62,f107,f87,f52])).

fof(f554,plain,
    ( spl5_64
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f199,f110,f105,f85,f75,f65,f60,f551])).

fof(f551,plain,
    ( spl5_64
  <=> v1_pre_topc(k2_tsep_1(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f199,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK3,sK2))
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f62,f107,f87,f52])).

fof(f549,plain,
    ( spl5_63
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f198,f115,f105,f85,f75,f70,f60,f546])).

fof(f546,plain,
    ( spl5_63
  <=> v1_pre_topc(k2_tsep_1(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f198,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK3,sK1))
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f62,f107,f87,f52])).

fof(f544,plain,
    ( spl5_62
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f197,f110,f90,f85,f75,f65,f55,f541])).

fof(f541,plain,
    ( spl5_62
  <=> v1_pre_topc(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f197,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f67,f112,f87,f52])).

fof(f539,plain,
    ( spl5_61
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f196,f110,f105,f85,f75,f65,f60,f536])).

fof(f536,plain,
    ( spl5_61
  <=> v1_pre_topc(k2_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f196,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK2,sK3))
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f67,f112,f87,f52])).

fof(f534,plain,
    ( spl5_60
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f195,f110,f85,f75,f65,f531])).

fof(f531,plain,
    ( spl5_60
  <=> v1_pre_topc(k2_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f195,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK2,sK2))
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f67,f112,f87,f52])).

fof(f529,plain,
    ( spl5_59
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f194,f115,f110,f85,f75,f70,f65,f526])).

fof(f526,plain,
    ( spl5_59
  <=> v1_pre_topc(k2_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f194,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK2,sK1))
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f67,f112,f87,f52])).

fof(f524,plain,
    ( spl5_58
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f193,f115,f90,f85,f75,f70,f55,f521])).

fof(f521,plain,
    ( spl5_58
  <=> v1_pre_topc(k2_tsep_1(sK0,sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f193,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK1,sK4))
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f72,f117,f87,f52])).

fof(f519,plain,
    ( spl5_57
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f192,f115,f105,f85,f75,f70,f60,f516])).

fof(f516,plain,
    ( spl5_57
  <=> v1_pre_topc(k2_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f192,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK1,sK3))
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f72,f117,f87,f52])).

fof(f514,plain,
    ( spl5_56
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f191,f115,f110,f85,f75,f70,f65,f511])).

fof(f511,plain,
    ( spl5_56
  <=> v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f191,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f72,f117,f87,f52])).

fof(f509,plain,
    ( spl5_55
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f190,f115,f85,f75,f70,f506])).

fof(f506,plain,
    ( spl5_55
  <=> v1_pre_topc(k2_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f190,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK1,sK1))
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f72,f117,f87,f52])).

fof(f504,plain,
    ( ~ spl5_54
    | spl5_1
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f189,f90,f85,f75,f55,f501])).

fof(f501,plain,
    ( spl5_54
  <=> v2_struct_0(k2_tsep_1(sK0,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f189,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK4,sK4))
    | spl5_1
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f57,f92,f87,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f499,plain,
    ( ~ spl5_53
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f188,f105,f90,f85,f75,f60,f55,f496])).

fof(f496,plain,
    ( spl5_53
  <=> v2_struct_0(k2_tsep_1(sK0,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f188,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK4,sK3))
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f57,f92,f87,f51])).

fof(f494,plain,
    ( ~ spl5_52
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f187,f110,f90,f85,f75,f65,f55,f491])).

fof(f491,plain,
    ( spl5_52
  <=> v2_struct_0(k2_tsep_1(sK0,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f187,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK4,sK2))
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f57,f92,f87,f51])).

fof(f489,plain,
    ( ~ spl5_51
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f186,f115,f90,f85,f75,f70,f55,f486])).

fof(f486,plain,
    ( spl5_51
  <=> v2_struct_0(k2_tsep_1(sK0,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f186,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK4,sK1))
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f57,f92,f87,f51])).

fof(f484,plain,
    ( ~ spl5_50
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f185,f105,f90,f85,f75,f60,f55,f481])).

fof(f481,plain,
    ( spl5_50
  <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f185,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK4))
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f62,f107,f87,f51])).

fof(f479,plain,
    ( ~ spl5_49
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f184,f105,f85,f75,f60,f476])).

fof(f476,plain,
    ( spl5_49
  <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f184,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK3))
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f62,f107,f87,f51])).

fof(f474,plain,
    ( ~ spl5_48
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f183,f110,f105,f85,f75,f65,f60,f471])).

fof(f471,plain,
    ( spl5_48
  <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f183,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f62,f107,f87,f51])).

fof(f469,plain,
    ( ~ spl5_47
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f182,f115,f105,f85,f75,f70,f60,f466])).

fof(f466,plain,
    ( spl5_47
  <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f182,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f62,f107,f87,f51])).

fof(f464,plain,
    ( ~ spl5_46
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f181,f110,f90,f85,f75,f65,f55,f461])).

fof(f181,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f67,f112,f87,f51])).

fof(f459,plain,
    ( ~ spl5_45
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f180,f110,f105,f85,f75,f65,f60,f456])).

fof(f456,plain,
    ( spl5_45
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f180,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f67,f112,f87,f51])).

fof(f454,plain,
    ( ~ spl5_44
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f179,f110,f85,f75,f65,f451])).

fof(f451,plain,
    ( spl5_44
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f179,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK2))
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f67,f112,f87,f51])).

fof(f449,plain,
    ( ~ spl5_43
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f178,f115,f110,f85,f75,f70,f65,f446])).

fof(f446,plain,
    ( spl5_43
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f178,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f67,f112,f87,f51])).

fof(f444,plain,
    ( ~ spl5_42
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f177,f115,f90,f85,f75,f70,f55,f441])).

fof(f441,plain,
    ( spl5_42
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f177,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK4))
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f72,f117,f87,f51])).

fof(f439,plain,
    ( ~ spl5_41
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f176,f115,f105,f85,f75,f70,f60,f436])).

fof(f436,plain,
    ( spl5_41
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f176,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f72,f117,f87,f51])).

fof(f434,plain,
    ( ~ spl5_40
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f175,f115,f110,f85,f75,f70,f65,f431])).

fof(f431,plain,
    ( spl5_40
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f175,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f72,f117,f87,f51])).

fof(f429,plain,
    ( ~ spl5_39
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f174,f115,f85,f75,f70,f426])).

fof(f426,plain,
    ( spl5_39
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f174,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK1))
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f72,f117,f87,f51])).

fof(f424,plain,
    ( spl5_38
    | spl5_1
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f173,f90,f85,f75,f55,f421])).

fof(f421,plain,
    ( spl5_38
  <=> v1_pre_topc(k1_tsep_1(sK0,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f173,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK4,sK4))
    | spl5_1
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f57,f92,f87,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f419,plain,
    ( spl5_37
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f169,f105,f90,f85,f75,f60,f55,f416])).

fof(f416,plain,
    ( spl5_37
  <=> v1_pre_topc(k1_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f169,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK3,sK4))
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f62,f107,f87,f49])).

fof(f414,plain,
    ( spl5_36
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f168,f105,f85,f75,f60,f411])).

fof(f411,plain,
    ( spl5_36
  <=> v1_pre_topc(k1_tsep_1(sK0,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f168,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK3,sK3))
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f62,f107,f87,f49])).

fof(f409,plain,
    ( spl5_35
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f165,f110,f90,f85,f75,f65,f55,f406])).

fof(f406,plain,
    ( spl5_35
  <=> v1_pre_topc(k1_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f165,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK2,sK4))
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f67,f112,f87,f49])).

fof(f404,plain,
    ( spl5_34
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f164,f110,f105,f85,f75,f65,f60,f401])).

fof(f401,plain,
    ( spl5_34
  <=> v1_pre_topc(k1_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f164,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK2,sK3))
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f67,f112,f87,f49])).

fof(f399,plain,
    ( spl5_33
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f163,f110,f85,f75,f65,f396])).

fof(f396,plain,
    ( spl5_33
  <=> v1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f163,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK2,sK2))
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f67,f112,f87,f49])).

fof(f394,plain,
    ( spl5_32
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f161,f115,f90,f85,f75,f70,f55,f391])).

fof(f391,plain,
    ( spl5_32
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f161,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK4))
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f72,f117,f87,f49])).

fof(f389,plain,
    ( spl5_31
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f160,f115,f105,f85,f75,f70,f60,f386])).

fof(f386,plain,
    ( spl5_31
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f160,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f72,f117,f87,f49])).

fof(f384,plain,
    ( spl5_30
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f159,f115,f110,f85,f75,f70,f65,f381])).

fof(f381,plain,
    ( spl5_30
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f159,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f72,f117,f87,f49])).

fof(f379,plain,
    ( spl5_29
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f158,f115,f85,f75,f70,f376])).

fof(f376,plain,
    ( spl5_29
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f158,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK1))
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f72,f117,f87,f49])).

fof(f374,plain,
    ( ~ spl5_28
    | spl5_1
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f152,f90,f85,f75,f55,f371])).

fof(f371,plain,
    ( spl5_28
  <=> v2_struct_0(k1_tsep_1(sK0,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f152,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK4,sK4))
    | spl5_1
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f57,f92,f87,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f369,plain,
    ( ~ spl5_27
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f148,f105,f90,f85,f75,f60,f55,f366])).

fof(f366,plain,
    ( spl5_27
  <=> v2_struct_0(k1_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f148,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | spl5_1
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f62,f107,f87,f48])).

fof(f364,plain,
    ( ~ spl5_26
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f147,f105,f85,f75,f60,f361])).

fof(f361,plain,
    ( spl5_26
  <=> v2_struct_0(k1_tsep_1(sK0,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f147,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK3,sK3))
    | spl5_2
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f62,f107,f87,f48])).

fof(f359,plain,
    ( ~ spl5_25
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f144,f110,f90,f85,f75,f65,f55,f356])).

fof(f356,plain,
    ( spl5_25
  <=> v2_struct_0(k1_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f144,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK4))
    | spl5_1
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f67,f112,f87,f48])).

fof(f354,plain,
    ( ~ spl5_24
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f143,f110,f105,f85,f75,f65,f60,f351])).

fof(f351,plain,
    ( spl5_24
  <=> v2_struct_0(k1_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f143,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK3))
    | spl5_2
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f67,f112,f87,f48])).

fof(f349,plain,
    ( ~ spl5_23
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f142,f110,f85,f75,f65,f346])).

fof(f346,plain,
    ( spl5_23
  <=> v2_struct_0(k1_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f142,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK2))
    | spl5_3
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f67,f112,f87,f48])).

fof(f344,plain,
    ( ~ spl5_22
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f140,f115,f90,f85,f75,f70,f55,f341])).

fof(f341,plain,
    ( spl5_22
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f140,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK4))
    | spl5_1
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f57,f92,f72,f117,f87,f48])).

fof(f339,plain,
    ( ~ spl5_17
    | spl5_1
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f316,f120,f115,f110,f95,f90,f85,f80,f75,f70,f65,f55,f133])).

fof(f316,plain,
    ( ~ r1_tsep_1(sK2,sK4)
    | spl5_1
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(unit_resulting_resolution,[],[f67,f57,f122,f92,f97,f112,f72,f117,f87,f77,f82,f46])).

fof(f328,plain,
    ( ~ spl5_21
    | spl5_1
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f309,f120,f115,f110,f95,f90,f85,f80,f75,f70,f65,f55,f325])).

fof(f309,plain,
    ( ~ r1_tsep_1(sK4,sK2)
    | spl5_1
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(unit_resulting_resolution,[],[f67,f57,f122,f92,f97,f112,f72,f117,f87,f77,f82,f44])).

fof(f308,plain,
    ( ~ spl5_20
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f139,f115,f105,f85,f75,f70,f60,f305])).

fof(f139,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | spl5_2
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f62,f107,f72,f117,f87,f48])).

fof(f226,plain,
    ( ~ spl5_19
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f138,f115,f110,f85,f75,f70,f65,f223])).

fof(f223,plain,
    ( spl5_19
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f138,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f67,f112,f72,f117,f87,f48])).

fof(f157,plain,
    ( ~ spl5_18
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f137,f115,f85,f75,f70,f154])).

fof(f154,plain,
    ( spl5_18
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f137,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK1))
    | spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f77,f72,f117,f72,f117,f87,f48])).

fof(f136,plain,
    ( spl5_16
    | spl5_17 ),
    inference(avatar_split_clause,[],[f24,f133,f129])).

fof(f24,plain,
    ( r1_tsep_1(sK2,sK4)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f127,plain,
    ( ~ spl5_14
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f23,f124,f120])).

fof(f23,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(sK4,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f118,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f34,f115])).

fof(f34,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f113,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f32,f110])).

fof(f32,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f108,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f30,f105])).

fof(f30,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f103,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f28,f100])).

fof(f28,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f10])).

fof(f98,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f27,f95])).

fof(f27,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f93,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f26,f90])).

fof(f26,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f88,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f36,f80])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f78,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f73,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f33,f70])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
